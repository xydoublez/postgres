/*-------------------------------------------------------------------------
 *
 * cluster.c
 *    REPACK a table; formerly known as CLUSTER.  VACUUM FULL also uses
 *    parts of this code.
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994-5, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/commands/cluster.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/amapi.h"
#include "access/heapam.h"
#include "access/multixact.h"
#include "access/relscan.h"
#include "access/tableam.h"
#include "access/toast_internals.h"
#include "access/transam.h"
#include "access/xact.h"
#include "catalog/catalog.h"
#include "catalog/dependency.h"
#include "catalog/heap.h"
#include "catalog/index.h"
#include "catalog/namespace.h"
#include "catalog/objectaccess.h"
#include "catalog/pg_am.h"
#include "catalog/pg_inherits.h"
#include "catalog/toasting.h"
#include "commands/cluster.h"
#include "commands/defrem.h"
#include "commands/progress.h"
#include "commands/tablecmds.h"
#include "commands/vacuum.h"
#include "miscadmin.h"
#include "optimizer/optimizer.h"
#include "pgstat.h"
#include "storage/bufmgr.h"
#include "storage/lmgr.h"
#include "storage/predicate.h"
#include "utils/acl.h"
#include "utils/datum.h"
#include "utils/fmgroids.h"
#include "utils/guc.h"
#include "utils/inval.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"
#include "utils/pg_rusage.h"
#include "utils/relmapper.h"
#include "utils/snapmgr.h"
#include "utils/syscache.h"

/*
 * REPACK and REPACK CONCURRENTLY — Architecture Overview
 * =======================================================
 *
 * The REPACK command (and its predecessor CLUSTER) physically rewrites a
 * table's heap file, optionally reordering rows according to an index.
 * Two modes are available:
 *
 * 1. Standard REPACK (blocking)
 * ------------------------------
 * Acquires AccessExclusiveLock for the full duration.  No other session
 * can read or write the table while REPACK runs.
 *
 *   ExecRepack
 *     → process_single_relation      (acquire AccessExclusiveLock, resolve index)
 *       → cluster_rel                (recheck permissions, call rebuild_relation)
 *         → rebuild_relation         (make_new_heap → copy_table_data → finish_heap_swap)
 *
 * copy_table_data performs the actual heap rewrite: it opens the old heap
 * (and optionally an index) via a TableScanDesc, writes rows into the new
 * heap in sorted order using heap_insert(), and records the freeze XID and
 * cutoff MultiXact for use during the file swap.
 *
 * finish_heap_swap swaps the physical file identifiers of the old and new
 * heaps (via swap_relation_files), rebuilds all indexes on the old heap OID,
 * and then drops the transient new heap.
 *
 *
 * 2. REPACK CONCURRENTLY (non-blocking)
 * --------------------------------------
 * Minimises the exclusive-lock window so that DML (INSERT/UPDATE/DELETE) can
 * proceed on the table during the slow copy phase.  The implementation is
 * modeled on REINDEX CONCURRENTLY.
 *
 *   ExecRepack
 *     → process_single_relation      (acquire ShareUpdateExclusiveLock, resolve index)
 *       → repack_relation_concurrent (manages its own transaction lifecycle)
 *
 * repack_relation_concurrent uses a three-phase algorithm:
 *
 *   Phase 1  (ShareUpdateExclusiveLock)
 *   ────────────────────────────────────
 *   • make_new_heap creates a transient heap.
 *   • copy_table_data copies all currently-visible rows into the new heap.
 *   • phase1_snapshot_xmin = ReadNextTransactionId() is recorded immediately
 *     before the copy begins.  Any row whose committed xmin ≥ this value was
 *     inserted after Phase 1 started and will be handled in Phase 2.
 *   • A session-level ShareUpdateExclusiveLock is taken on the old heap to
 *     prevent it from being dropped across transaction boundaries.
 *   • Phase 1's transaction is committed; DML has been running freely.
 *
 *   Wait phase
 *   ──────────
 *   • WaitForLockers blocks until all transactions that held any lock on the
 *     old heap at the time Phase 1 committed have either committed or rolled
 *     back.  This guarantees that no in-flight DML is still modifying the old
 *     heap when we acquire AccessExclusiveLock in Phase 2.
 *
 *   Phase 2  (AccessExclusiveLock)
 *   ────────────────────────────────
 *   • Reopen the old heap with AccessExclusiveLock (blocks new DML).
 *   • Apply the "delta" — changes to the old heap that occurred after Phase 1:
 *       New inserts: scan old heap with current snapshot; any live row whose
 *         committed xmin ≥ phase1_snapshot_xmin was inserted after Phase 1 and
 *         is absent from the new heap → insert a copy into the new heap.
 *       Phantom deletes: scan old heap with SnapshotAny; a row committed before
 *         Phase 1 (xmin < phase1_snapshot_xmin) that has a committed deletion
 *         (xmax ≥ phase1_snapshot_xmin) was copied into the new heap in Phase 1
 *         but should no longer exist → find the matching row in the new heap by
 *         attribute-wise equality (tuples_are_equal) and delete it.
 *   • finish_heap_swap swaps heap files and rebuilds indexes, as in standard
 *     REPACK.
 *   • The session-level lock is released and a new transaction is started so
 *     that the outer command loop can perform its own CommitTransactionCommand.
 *
 * Key helper functions
 * ─────────────────────
 *   make_new_heap          — creates an empty transient heap with identical
 *                            schema, TOAST table, and storage options.
 *   copy_table_data        — sequential/index scan + write to new heap; sets
 *                            freeze XID and cutoff MultiXact values.
 *   finish_heap_swap       — swaps file nodes, renames TOAST tables, rebuilds
 *                            indexes, drops transient heap.
 *   tuples_are_equal       — attribute-by-attribute equality check used for
 *                            delta-reconciliation; handles NULLs and detoasts
 *                            variable-length values before comparison.
 *
 * Restrictions on REPACK CONCURRENTLY
 * ─────────────────────────────────────
 *   • Must name a specific table (cannot repack all tables at once).
 *   • Cannot run inside a transaction block.
 *   • Not supported for CLUSTER or VACUUM FULL commands.
 *   • Not supported with ANALYZE.
 *   • Not supported on system catalogs, shared relations, temporary tables of
 *     other sessions, or partitioned tables.
 */

/*
 * This struct is used to pass around the information on tables to be
 * clustered. We need this so we can make a list of them when invoked without
 * a specific table/index pair.
 */
typedef struct
{
	Oid			tableOid;
	Oid			indexOid;
} RelToCluster;

static bool cluster_rel_recheck(RepackCommand cmd, Relation OldHeap,
								Oid indexOid, Oid userid, int options);
static void rebuild_relation(Relation OldHeap, Relation index, bool verbose);
static void copy_table_data(Relation NewHeap, Relation OldHeap, Relation OldIndex,
							bool verbose, bool *pSwapToastByContent,
							TransactionId *pFreezeXid, MultiXactId *pCutoffMulti);
static List *get_tables_to_repack(RepackCommand cmd, bool usingindex,
								  MemoryContext permcxt);
static List *get_tables_to_repack_partitioned(RepackCommand cmd,
											  Oid relid, bool rel_is_index,
											  MemoryContext permcxt);
static bool repack_is_permitted_for_relation(RepackCommand cmd,
											 Oid relid, Oid userid);
static Relation process_single_relation(RepackStmt *stmt,
										ClusterParams *params);
static Oid	determine_clustered_index(Relation rel, bool usingindex,
									  const char *indexname);
static const char *RepackCommandAsString(RepackCommand cmd);
static void repack_relation_concurrent(Oid tableOid, Oid indexOid,
									   ClusterParams *params);
static bool tuples_are_equal(TupleDesc tupdesc, HeapTuple tup1, HeapTuple tup2);


/*
 * The repack code allows for processing multiple tables at once. Because
 * of this, we cannot just run everything on a single transaction, or we
 * would be forced to acquire exclusive locks on all the tables being
 * clustered, simultaneously --- very likely leading to deadlock.
 *
 * To solve this we follow a similar strategy to VACUUM code, processing each
 * relation in a separate transaction. For this to work, we need to:
 *
 *	- provide a separate memory context so that we can pass information in
 *	  a way that survives across transactions
 *	- start a new transaction every time a new relation is clustered
 *	- check for validity of the information on to-be-clustered relations,
 *	  as someone might have deleted a relation behind our back, or
 *	  clustered one on a different index
 *	- end the transaction
 *
 * The single-relation case does not have any such overhead.
 *
 * We also allow a relation to be repacked following an index, but without
 * naming a specific one.  In that case, the indisclustered bit will be
 * looked up, and an ERROR will be thrown if no so-marked index is found.
 */
void
ExecRepack(ParseState *pstate, RepackStmt *stmt, bool isTopLevel)
{
	ClusterParams params = {0};
	Relation	rel = NULL;
	MemoryContext repack_context;
	List	   *rtcs;

	/* Parse option list */
	foreach_node(DefElem, opt, stmt->params)
	{
		if (strcmp(opt->defname, "verbose") == 0)
			params.options |= defGetBoolean(opt) ? CLUOPT_VERBOSE : 0;
		else if (strcmp(opt->defname, "analyze") == 0 ||
				 strcmp(opt->defname, "analyse") == 0)
			params.options |= defGetBoolean(opt) ? CLUOPT_ANALYZE : 0;
		else if (strcmp(opt->defname, "concurrently") == 0)
			params.options |= CLUOPT_CONCURRENT;
		else
			ereport(ERROR,
					errcode(ERRCODE_SYNTAX_ERROR),
					errmsg("unrecognized %s option \"%s\"",
						   RepackCommandAsString(stmt->command),
						   opt->defname),
					parser_errposition(pstate, opt->location));
	}

	/* CONCURRENTLY has several restrictions */
	if (params.options & CLUOPT_CONCURRENT)
	{
		/*
		 * REPACK CONCURRENTLY is only supported for the REPACK command, not
		 * for the legacy CLUSTER command or VACUUM FULL.
		 */
		if (stmt->command != REPACK_COMMAND_REPACK)
			ereport(ERROR,
					errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					errmsg("CONCURRENTLY is not supported for %s",
						   RepackCommandAsString(stmt->command)));

		/*
		 * CONCURRENTLY requires a specific relation to be named; repacking
		 * all tables at once concurrently is not supported.
		 */
		if (stmt->relation == NULL)
			ereport(ERROR,
					errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					errmsg("REPACK CONCURRENTLY requires a table name"));

		/*
		 * ANALYZE with CONCURRENTLY is not currently supported.
		 */
		if (params.options & CLUOPT_ANALYZE)
			ereport(ERROR,
					errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					errmsg("REPACK CONCURRENTLY is not supported with ANALYZE"));

		/*
		 * CONCURRENTLY cannot run inside a transaction block.
		 */
		PreventInTransactionBlock(isTopLevel, "REPACK CONCURRENTLY");
	}

	/*
	 * If a single relation is specified, process it and we're done ... unless
	 * the relation is a partitioned table, in which case we fall through.
	 */
	if (stmt->relation != NULL)
	{
		rel = process_single_relation(stmt, &params);
		if (rel == NULL)
			return;				/* all done */
	}

	/*
	 * Don't allow ANALYZE in the multiple-relation case for now.  Maybe we
	 * can add support for this later.
	 */
	if (params.options & CLUOPT_ANALYZE)
		ereport(ERROR,
				errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				errmsg("cannot execute %s on multiple tables",
					   "REPACK (ANALYZE)"));

	/*
	 * By here, we know we are in a multi-table situation.  In order to avoid
	 * holding locks for too long, we want to process each table in its own
	 * transaction.  This forces us to disallow running inside a user
	 * transaction block.
	 */
	PreventInTransactionBlock(isTopLevel, RepackCommandAsString(stmt->command));

	/* Also, we need a memory context to hold our list of relations */
	repack_context = AllocSetContextCreate(PortalContext,
										   "Repack",
										   ALLOCSET_DEFAULT_SIZES);

	params.options |= CLUOPT_RECHECK;

	/*
	 * If we don't have a relation yet, determine a relation list.  If we do,
	 * then it must be a partitioned table, and we want to process its
	 * partitions.
	 */
	if (rel == NULL)
	{
		Assert(stmt->indexname == NULL);
		rtcs = get_tables_to_repack(stmt->command, stmt->usingindex,
									repack_context);
		params.options |= CLUOPT_RECHECK_ISCLUSTERED;
	}
	else
	{
		Oid			relid;
		bool		rel_is_index;

		Assert(rel->rd_rel->relkind == RELKIND_PARTITIONED_TABLE);

		/*
		 * If USING INDEX was specified, resolve the index name now and pass
		 * it down.
		 */
		if (stmt->usingindex)
		{
			/*
			 * If no index name was specified when repacking a partitioned
			 * table, punt for now.  Maybe we can improve this later.
			 */
			if (!stmt->indexname)
			{
				if (stmt->command == REPACK_COMMAND_CLUSTER)
					ereport(ERROR,
							errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
							errmsg("there is no previously clustered index for table \"%s\"",
								   RelationGetRelationName(rel)));
				else
					ereport(ERROR,
							errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
					/*- translator: first %s is name of a SQL command, eg. REPACK */
							errmsg("cannot execute %s on partitioned table \"%s\" USING INDEX with no index name",
								   RepackCommandAsString(stmt->command),
								   RelationGetRelationName(rel)));
			}

			relid = determine_clustered_index(rel, stmt->usingindex,
											  stmt->indexname);
			if (!OidIsValid(relid))
				elog(ERROR, "unable to determine index to cluster on");
			check_index_is_clusterable(rel, relid, AccessExclusiveLock);

			rel_is_index = true;
		}
		else
		{
			relid = RelationGetRelid(rel);
			rel_is_index = false;
		}

		rtcs = get_tables_to_repack_partitioned(stmt->command,
												relid, rel_is_index,
												repack_context);

		/* close parent relation, releasing lock on it */
		table_close(rel, AccessExclusiveLock);
		rel = NULL;
	}

	/* Commit to get out of starting transaction */
	PopActiveSnapshot();
	CommitTransactionCommand();

	/* Cluster the tables, each in a separate transaction */
	Assert(rel == NULL);
	foreach_ptr(RelToCluster, rtc, rtcs)
	{
		/* Start a new transaction for each relation. */
		StartTransactionCommand();

		/*
		 * Open the target table, coping with the case where it has been
		 * dropped.
		 */
		rel = try_table_open(rtc->tableOid, AccessExclusiveLock);
		if (rel == NULL)
		{
			CommitTransactionCommand();
			continue;
		}

		/* functions in indexes may want a snapshot set */
		PushActiveSnapshot(GetTransactionSnapshot());

		/* Process this table */
		cluster_rel(stmt->command, rel, rtc->indexOid, &params);
		/* cluster_rel closes the relation, but keeps lock */

		PopActiveSnapshot();
		CommitTransactionCommand();
	}

	/* Start a new transaction for the cleanup work. */
	StartTransactionCommand();

	/* Clean up working storage */
	MemoryContextDelete(repack_context);
}

/*
 * cluster_rel
 *
 * This clusters the table by creating a new, clustered table and
 * swapping the relfilenumbers of the new table and the old table, so
 * the OID of the original table is preserved.  Thus we do not lose
 * GRANT, inheritance nor references to this table.
 *
 * Indexes are rebuilt too, via REINDEX. Since we are effectively bulk-loading
 * the new table, it's better to create the indexes afterwards than to fill
 * them incrementally while we load the table.
 *
 * If indexOid is InvalidOid, the table will be rewritten in physical order
 * instead of index order.
 *
 * 'cmd' indicates which command is being executed, to be used for error
 * messages.
 */
void
cluster_rel(RepackCommand cmd, Relation OldHeap, Oid indexOid,
			ClusterParams *params)
{
	Oid			tableOid = RelationGetRelid(OldHeap);
	Oid			save_userid;
	int			save_sec_context;
	int			save_nestlevel;
	bool		verbose = ((params->options & CLUOPT_VERBOSE) != 0);
	bool		recheck = ((params->options & CLUOPT_RECHECK) != 0);
	Relation	index;

	Assert(CheckRelationLockedByMe(OldHeap, AccessExclusiveLock, false));

	/* Check for user-requested abort. */
	CHECK_FOR_INTERRUPTS();

	pgstat_progress_start_command(PROGRESS_COMMAND_REPACK, tableOid);
	pgstat_progress_update_param(PROGRESS_REPACK_COMMAND, cmd);

	/*
	 * Switch to the table owner's userid, so that any index functions are run
	 * as that user.  Also lock down security-restricted operations and
	 * arrange to make GUC variable changes local to this command.
	 */
	GetUserIdAndSecContext(&save_userid, &save_sec_context);
	SetUserIdAndSecContext(OldHeap->rd_rel->relowner,
						   save_sec_context | SECURITY_RESTRICTED_OPERATION);
	save_nestlevel = NewGUCNestLevel();
	RestrictSearchPath();

	/*
	 * Since we may open a new transaction for each relation, we have to check
	 * that the relation still is what we think it is.
	 *
	 * If this is a single-transaction CLUSTER, we can skip these tests. We
	 * *must* skip the one on indisclustered since it would reject an attempt
	 * to cluster a not-previously-clustered index.
	 */
	if (recheck &&
		!cluster_rel_recheck(cmd, OldHeap, indexOid, save_userid,
							 params->options))
		goto out;

	/*
	 * We allow repacking shared catalogs only when not using an index. It
	 * would work to use an index in most respects, but the index would only
	 * get marked as indisclustered in the current database, leading to
	 * unexpected behavior if CLUSTER were later invoked in another database.
	 */
	if (OidIsValid(indexOid) && OldHeap->rd_rel->relisshared)
		ereport(ERROR,
				errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
		/*- translator: first %s is name of a SQL command, eg. REPACK */
				errmsg("cannot execute %s on a shared catalog",
					   RepackCommandAsString(cmd)));

	/*
	 * Don't process temp tables of other backends ... their local buffer
	 * manager is not going to cope.
	 */
	if (RELATION_IS_OTHER_TEMP(OldHeap))
		ereport(ERROR,
				errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
		/*- translator: first %s is name of a SQL command, eg. REPACK */
				errmsg("cannot execute %s on temporary tables of other sessions",
					   RepackCommandAsString(cmd)));

	/*
	 * Also check for active uses of the relation in the current transaction,
	 * including open scans and pending AFTER trigger events.
	 */
	CheckTableNotInUse(OldHeap, RepackCommandAsString(cmd));

	/* Check heap and index are valid to cluster on */
	if (OidIsValid(indexOid))
	{
		/* verify the index is good and lock it */
		check_index_is_clusterable(OldHeap, indexOid, AccessExclusiveLock);
		/* also open it */
		index = index_open(indexOid, NoLock);
	}
	else
		index = NULL;

	/*
	 * When allow_system_table_mods is turned off, we disallow repacking a
	 * catalog on a particular index unless that's already the clustered index
	 * for that catalog.
	 *
	 * XXX We don't check for this in CLUSTER, because it's historically been
	 * allowed.
	 */
	if (cmd != REPACK_COMMAND_CLUSTER &&
		!allowSystemTableMods && OidIsValid(indexOid) &&
		IsCatalogRelation(OldHeap) && !index->rd_index->indisclustered)
		ereport(ERROR,
				errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
				errmsg("permission denied: \"%s\" is a system catalog",
					   RelationGetRelationName(OldHeap)),
				errdetail("System catalogs can only be clustered by the index they're already clustered on, if any, unless \"%s\" is enabled.",
						  "allow_system_table_mods"));

	/*
	 * Quietly ignore the request if this is a materialized view which has not
	 * been populated from its query. No harm is done because there is no data
	 * to deal with, and we don't want to throw an error if this is part of a
	 * multi-relation request -- for example, CLUSTER was run on the entire
	 * database.
	 */
	if (OldHeap->rd_rel->relkind == RELKIND_MATVIEW &&
		!RelationIsPopulated(OldHeap))
	{
		relation_close(OldHeap, AccessExclusiveLock);
		goto out;
	}

	Assert(OldHeap->rd_rel->relkind == RELKIND_RELATION ||
		   OldHeap->rd_rel->relkind == RELKIND_MATVIEW ||
		   OldHeap->rd_rel->relkind == RELKIND_TOASTVALUE);

	/*
	 * All predicate locks on the tuples or pages are about to be made
	 * invalid, because we move tuples around.  Promote them to relation
	 * locks.  Predicate locks on indexes will be promoted when they are
	 * reindexed.
	 */
	TransferPredicateLocksToHeapRelation(OldHeap);

	/* rebuild_relation does all the dirty work */
	rebuild_relation(OldHeap, index, verbose);
	/* rebuild_relation closes OldHeap, and index if valid */

out:
	/* Roll back any GUC changes executed by index functions */
	AtEOXact_GUC(false, save_nestlevel);

	/* Restore userid and security context */
	SetUserIdAndSecContext(save_userid, save_sec_context);

	pgstat_progress_end_command();
}

/*
 * Check if the table (and its index) still meets the requirements of
 * cluster_rel().
 */
static bool
cluster_rel_recheck(RepackCommand cmd, Relation OldHeap, Oid indexOid,
					Oid userid, int options)
{
	Oid			tableOid = RelationGetRelid(OldHeap);

	/* Check that the user still has privileges for the relation */
	if (!repack_is_permitted_for_relation(cmd, tableOid, userid))
	{
		relation_close(OldHeap, AccessExclusiveLock);
		return false;
	}

	/*
	 * Silently skip a temp table for a remote session.  Only doing this check
	 * in the "recheck" case is appropriate (which currently means somebody is
	 * executing a database-wide CLUSTER or on a partitioned table), because
	 * there is another check in cluster() which will stop any attempt to
	 * cluster remote temp tables by name.  There is another check in
	 * cluster_rel which is redundant, but we leave it for extra safety.
	 */
	if (RELATION_IS_OTHER_TEMP(OldHeap))
	{
		relation_close(OldHeap, AccessExclusiveLock);
		return false;
	}

	if (OidIsValid(indexOid))
	{
		/*
		 * Check that the index still exists
		 */
		if (!SearchSysCacheExists1(RELOID, ObjectIdGetDatum(indexOid)))
		{
			relation_close(OldHeap, AccessExclusiveLock);
			return false;
		}

		/*
		 * Check that the index is still the one with indisclustered set, if
		 * needed.
		 */
		if ((options & CLUOPT_RECHECK_ISCLUSTERED) != 0 &&
			!get_index_isclustered(indexOid))
		{
			relation_close(OldHeap, AccessExclusiveLock);
			return false;
		}
	}

	return true;
}

/*
 * Verify that the specified heap and index are valid to cluster on
 *
 * Side effect: obtains lock on the index.  The caller may
 * in some cases already have AccessExclusiveLock on the table, but
 * not in all cases so we can't rely on the table-level lock for
 * protection here.
 */
void
check_index_is_clusterable(Relation OldHeap, Oid indexOid, LOCKMODE lockmode)
{
	Relation	OldIndex;

	OldIndex = index_open(indexOid, lockmode);

	/*
	 * Check that index is in fact an index on the given relation
	 */
	if (OldIndex->rd_index == NULL ||
		OldIndex->rd_index->indrelid != RelationGetRelid(OldHeap))
		ereport(ERROR,
				(errcode(ERRCODE_WRONG_OBJECT_TYPE),
				 errmsg("\"%s\" is not an index for table \"%s\"",
						RelationGetRelationName(OldIndex),
						RelationGetRelationName(OldHeap))));

	/* Index AM must allow clustering */
	if (!OldIndex->rd_indam->amclusterable)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("cannot cluster on index \"%s\" because access method does not support clustering",
						RelationGetRelationName(OldIndex))));

	/*
	 * Disallow clustering on incomplete indexes (those that might not index
	 * every row of the relation).  We could relax this by making a separate
	 * seqscan pass over the table to copy the missing rows, but that seems
	 * expensive and tedious.
	 */
	if (!heap_attisnull(OldIndex->rd_indextuple, Anum_pg_index_indpred, NULL))
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("cannot cluster on partial index \"%s\"",
						RelationGetRelationName(OldIndex))));

	/*
	 * Disallow if index is left over from a failed CREATE INDEX CONCURRENTLY;
	 * it might well not contain entries for every heap row, or might not even
	 * be internally consistent.  (But note that we don't check indcheckxmin;
	 * the worst consequence of following broken HOT chains would be that we
	 * might put recently-dead tuples out-of-order in the new table, and there
	 * is little harm in that.)
	 */
	if (!OldIndex->rd_index->indisvalid)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("cannot cluster on invalid index \"%s\"",
						RelationGetRelationName(OldIndex))));

	/* Drop relcache refcnt on OldIndex, but keep lock */
	index_close(OldIndex, NoLock);
}

/*
 * mark_index_clustered: mark the specified index as the one clustered on
 *
 * With indexOid == InvalidOid, will mark all indexes of rel not-clustered.
 */
void
mark_index_clustered(Relation rel, Oid indexOid, bool is_internal)
{
	HeapTuple	indexTuple;
	Form_pg_index indexForm;
	Relation	pg_index;
	ListCell   *index;

	Assert(rel->rd_rel->relkind != RELKIND_PARTITIONED_TABLE);

	/*
	 * If the index is already marked clustered, no need to do anything.
	 */
	if (OidIsValid(indexOid))
	{
		if (get_index_isclustered(indexOid))
			return;
	}

	/*
	 * Check each index of the relation and set/clear the bit as needed.
	 */
	pg_index = table_open(IndexRelationId, RowExclusiveLock);

	foreach(index, RelationGetIndexList(rel))
	{
		Oid			thisIndexOid = lfirst_oid(index);

		indexTuple = SearchSysCacheCopy1(INDEXRELID,
										 ObjectIdGetDatum(thisIndexOid));
		if (!HeapTupleIsValid(indexTuple))
			elog(ERROR, "cache lookup failed for index %u", thisIndexOid);
		indexForm = (Form_pg_index) GETSTRUCT(indexTuple);

		/*
		 * Unset the bit if set.  We know it's wrong because we checked this
		 * earlier.
		 */
		if (indexForm->indisclustered)
		{
			indexForm->indisclustered = false;
			CatalogTupleUpdate(pg_index, &indexTuple->t_self, indexTuple);
		}
		else if (thisIndexOid == indexOid)
		{
			/* this was checked earlier, but let's be real sure */
			if (!indexForm->indisvalid)
				elog(ERROR, "cannot cluster on invalid index %u", indexOid);
			indexForm->indisclustered = true;
			CatalogTupleUpdate(pg_index, &indexTuple->t_self, indexTuple);
		}

		InvokeObjectPostAlterHookArg(IndexRelationId, thisIndexOid, 0,
									 InvalidOid, is_internal);

		heap_freetuple(indexTuple);
	}

	table_close(pg_index, RowExclusiveLock);
}

/*
 * rebuild_relation: rebuild an existing relation in index or physical order
 *
 * OldHeap: table to rebuild.
 * index: index to cluster by, or NULL to rewrite in physical order.
 *
 * On entry, heap and index (if one is given) must be open, and
 * AccessExclusiveLock held on them.
 * On exit, they are closed, but locks on them are not released.
 */
static void
rebuild_relation(Relation OldHeap, Relation index, bool verbose)
{
	Oid			tableOid = RelationGetRelid(OldHeap);
	Oid			accessMethod = OldHeap->rd_rel->relam;
	Oid			tableSpace = OldHeap->rd_rel->reltablespace;
	Oid			OIDNewHeap;
	Relation	NewHeap;
	char		relpersistence;
	bool		is_system_catalog;
	bool		swap_toast_by_content;
	TransactionId frozenXid;
	MultiXactId cutoffMulti;

	Assert(CheckRelationLockedByMe(OldHeap, AccessExclusiveLock, false) &&
		   (index == NULL || CheckRelationLockedByMe(index, AccessExclusiveLock, false)));

	/* for CLUSTER or REPACK USING INDEX, mark the index as the one to use */
	if (index != NULL)
		mark_index_clustered(OldHeap, RelationGetRelid(index), true);

	/* Remember info about rel before closing OldHeap */
	relpersistence = OldHeap->rd_rel->relpersistence;
	is_system_catalog = IsSystemRelation(OldHeap);

	/*
	 * Create the transient table that will receive the re-ordered data.
	 *
	 * OldHeap is already locked, so no need to lock it again.  make_new_heap
	 * obtains AccessExclusiveLock on the new heap and its toast table.
	 */
	OIDNewHeap = make_new_heap(tableOid, tableSpace,
							   accessMethod,
							   relpersistence,
							   NoLock);
	Assert(CheckRelationOidLockedByMe(OIDNewHeap, AccessExclusiveLock, false));
	NewHeap = table_open(OIDNewHeap, NoLock);

	/* Copy the heap data into the new table in the desired order */
	copy_table_data(NewHeap, OldHeap, index, verbose,
					&swap_toast_by_content, &frozenXid, &cutoffMulti);


	/* Close relcache entries, but keep lock until transaction commit */
	table_close(OldHeap, NoLock);
	if (index)
		index_close(index, NoLock);

	/*
	 * Close the new relation so it can be dropped as soon as the storage is
	 * swapped. The relation is not visible to others, so no need to unlock it
	 * explicitly.
	 */
	table_close(NewHeap, NoLock);

	/*
	 * Swap the physical files of the target and transient tables, then
	 * rebuild the target's indexes and throw away the transient table.
	 */
	finish_heap_swap(tableOid, OIDNewHeap, is_system_catalog,
					 swap_toast_by_content, false, true,
					 frozenXid, cutoffMulti,
					 relpersistence);
}


/*
 * Create the transient table that will be filled with new data during
 * CLUSTER, ALTER TABLE, and similar operations.  The transient table
 * duplicates the logical structure of the OldHeap; but will have the
 * specified physical storage properties NewTableSpace, NewAccessMethod, and
 * relpersistence.
 *
 * After this, the caller should load the new heap with transferred/modified
 * data, then call finish_heap_swap to complete the operation.
 */
Oid
make_new_heap(Oid OIDOldHeap, Oid NewTableSpace, Oid NewAccessMethod,
			  char relpersistence, LOCKMODE lockmode)
{
	TupleDesc	OldHeapDesc;
	char		NewHeapName[NAMEDATALEN];
	Oid			OIDNewHeap;
	Oid			toastid;
	Relation	OldHeap;
	HeapTuple	tuple;
	Datum		reloptions;
	bool		isNull;
	Oid			namespaceid;

	OldHeap = table_open(OIDOldHeap, lockmode);
	OldHeapDesc = RelationGetDescr(OldHeap);

	/*
	 * Note that the NewHeap will not receive any of the defaults or
	 * constraints associated with the OldHeap; we don't need 'em, and there's
	 * no reason to spend cycles inserting them into the catalogs only to
	 * delete them.
	 */

	/*
	 * But we do want to use reloptions of the old heap for new heap.
	 */
	tuple = SearchSysCache1(RELOID, ObjectIdGetDatum(OIDOldHeap));
	if (!HeapTupleIsValid(tuple))
		elog(ERROR, "cache lookup failed for relation %u", OIDOldHeap);
	reloptions = SysCacheGetAttr(RELOID, tuple, Anum_pg_class_reloptions,
								 &isNull);
	if (isNull)
		reloptions = (Datum) 0;

	if (relpersistence == RELPERSISTENCE_TEMP)
		namespaceid = LookupCreationNamespace("pg_temp");
	else
		namespaceid = RelationGetNamespace(OldHeap);

	/*
	 * Create the new heap, using a temporary name in the same namespace as
	 * the existing table.  NOTE: there is some risk of collision with user
	 * relnames.  Working around this seems more trouble than it's worth; in
	 * particular, we can't create the new heap in a different namespace from
	 * the old, or we will have problems with the TEMP status of temp tables.
	 *
	 * Note: the new heap is not a shared relation, even if we are rebuilding
	 * a shared rel.  However, we do make the new heap mapped if the source is
	 * mapped.  This simplifies swap_relation_files, and is absolutely
	 * necessary for rebuilding pg_class, for reasons explained there.
	 */
	snprintf(NewHeapName, sizeof(NewHeapName), "pg_temp_%u", OIDOldHeap);

	OIDNewHeap = heap_create_with_catalog(NewHeapName,
										  namespaceid,
										  NewTableSpace,
										  InvalidOid,
										  InvalidOid,
										  InvalidOid,
										  OldHeap->rd_rel->relowner,
										  NewAccessMethod,
										  OldHeapDesc,
										  NIL,
										  RELKIND_RELATION,
										  relpersistence,
										  false,
										  RelationIsMapped(OldHeap),
										  ONCOMMIT_NOOP,
										  reloptions,
										  false,
										  true,
										  true,
										  OIDOldHeap,
										  NULL);
	Assert(OIDNewHeap != InvalidOid);

	ReleaseSysCache(tuple);

	/*
	 * Advance command counter so that the newly-created relation's catalog
	 * tuples will be visible to table_open.
	 */
	CommandCounterIncrement();

	/*
	 * If necessary, create a TOAST table for the new relation.
	 *
	 * If the relation doesn't have a TOAST table already, we can't need one
	 * for the new relation.  The other way around is possible though: if some
	 * wide columns have been dropped, NewHeapCreateToastTable can decide that
	 * no TOAST table is needed for the new table.
	 *
	 * Note that NewHeapCreateToastTable ends with CommandCounterIncrement, so
	 * that the TOAST table will be visible for insertion.
	 */
	toastid = OldHeap->rd_rel->reltoastrelid;
	if (OidIsValid(toastid))
	{
		/* keep the existing toast table's reloptions, if any */
		tuple = SearchSysCache1(RELOID, ObjectIdGetDatum(toastid));
		if (!HeapTupleIsValid(tuple))
			elog(ERROR, "cache lookup failed for relation %u", toastid);
		reloptions = SysCacheGetAttr(RELOID, tuple, Anum_pg_class_reloptions,
									 &isNull);
		if (isNull)
			reloptions = (Datum) 0;

		NewHeapCreateToastTable(OIDNewHeap, reloptions, lockmode, toastid);

		ReleaseSysCache(tuple);
	}

	table_close(OldHeap, NoLock);

	return OIDNewHeap;
}

/*
 * Do the physical copying of table data.
 *
 * There are three output parameters:
 * *pSwapToastByContent is set true if toast tables must be swapped by content.
 * *pFreezeXid receives the TransactionId used as freeze cutoff point.
 * *pCutoffMulti receives the MultiXactId used as a cutoff point.
 */
static void
copy_table_data(Relation NewHeap, Relation OldHeap, Relation OldIndex, bool verbose,
				bool *pSwapToastByContent, TransactionId *pFreezeXid,
				MultiXactId *pCutoffMulti)
{
	Relation	relRelation;
	HeapTuple	reltup;
	Form_pg_class relform;
	TupleDesc	oldTupDesc PG_USED_FOR_ASSERTS_ONLY;
	TupleDesc	newTupDesc PG_USED_FOR_ASSERTS_ONLY;
	VacuumParams params;
	struct VacuumCutoffs cutoffs;
	bool		use_sort;
	double		num_tuples = 0,
				tups_vacuumed = 0,
				tups_recently_dead = 0;
	BlockNumber num_pages;
	int			elevel = verbose ? INFO : DEBUG2;
	PGRUsage	ru0;
	char	   *nspname;

	pg_rusage_init(&ru0);

	/* Store a copy of the namespace name for logging purposes */
	nspname = get_namespace_name(RelationGetNamespace(OldHeap));

	/*
	 * Their tuple descriptors should be exactly alike, but here we only need
	 * assume that they have the same number of columns.
	 */
	oldTupDesc = RelationGetDescr(OldHeap);
	newTupDesc = RelationGetDescr(NewHeap);
	Assert(newTupDesc->natts == oldTupDesc->natts);

	/*
	 * If the OldHeap has a toast table, get lock on the toast table to keep
	 * it from being vacuumed.  This is needed because autovacuum processes
	 * toast tables independently of their main tables, with no lock on the
	 * latter.  If an autovacuum were to start on the toast table after we
	 * compute our OldestXmin below, it would use a later OldestXmin, and then
	 * possibly remove as DEAD toast tuples belonging to main tuples we think
	 * are only RECENTLY_DEAD.  Then we'd fail while trying to copy those
	 * tuples.
	 *
	 * We don't need to open the toast relation here, just lock it.  The lock
	 * will be held till end of transaction.
	 */
	if (OldHeap->rd_rel->reltoastrelid)
		LockRelationOid(OldHeap->rd_rel->reltoastrelid, AccessExclusiveLock);

	/*
	 * If both tables have TOAST tables, perform toast swap by content.  It is
	 * possible that the old table has a toast table but the new one doesn't,
	 * if toastable columns have been dropped.  In that case we have to do
	 * swap by links.  This is okay because swap by content is only essential
	 * for system catalogs, and we don't support schema changes for them.
	 */
	if (OldHeap->rd_rel->reltoastrelid && NewHeap->rd_rel->reltoastrelid)
	{
		*pSwapToastByContent = true;

		/*
		 * When doing swap by content, any toast pointers written into NewHeap
		 * must use the old toast table's OID, because that's where the toast
		 * data will eventually be found.  Set this up by setting rd_toastoid.
		 * This also tells toast_save_datum() to preserve the toast value
		 * OIDs, which we want so as not to invalidate toast pointers in
		 * system catalog caches, and to avoid making multiple copies of a
		 * single toast value.
		 *
		 * Note that we must hold NewHeap open until we are done writing data,
		 * since the relcache will not guarantee to remember this setting once
		 * the relation is closed.  Also, this technique depends on the fact
		 * that no one will try to read from the NewHeap until after we've
		 * finished writing it and swapping the rels --- otherwise they could
		 * follow the toast pointers to the wrong place.  (It would actually
		 * work for values copied over from the old toast table, but not for
		 * any values that we toast which were previously not toasted.)
		 */
		NewHeap->rd_toastoid = OldHeap->rd_rel->reltoastrelid;
	}
	else
		*pSwapToastByContent = false;

	/*
	 * Compute xids used to freeze and weed out dead tuples and multixacts.
	 * Since we're going to rewrite the whole table anyway, there's no reason
	 * not to be aggressive about this.
	 */
	memset(&params, 0, sizeof(VacuumParams));
	vacuum_get_cutoffs(OldHeap, params, &cutoffs);

	/*
	 * FreezeXid will become the table's new relfrozenxid, and that mustn't go
	 * backwards, so take the max.
	 */
	{
		TransactionId relfrozenxid = OldHeap->rd_rel->relfrozenxid;

		if (TransactionIdIsValid(relfrozenxid) &&
			TransactionIdPrecedes(cutoffs.FreezeLimit, relfrozenxid))
			cutoffs.FreezeLimit = relfrozenxid;
	}

	/*
	 * MultiXactCutoff, similarly, shouldn't go backwards either.
	 */
	{
		MultiXactId relminmxid = OldHeap->rd_rel->relminmxid;

		if (MultiXactIdIsValid(relminmxid) &&
			MultiXactIdPrecedes(cutoffs.MultiXactCutoff, relminmxid))
			cutoffs.MultiXactCutoff = relminmxid;
	}

	/*
	 * Decide whether to use an indexscan or seqscan-and-optional-sort to scan
	 * the OldHeap.  We know how to use a sort to duplicate the ordering of a
	 * btree index, and will use seqscan-and-sort for that case if the planner
	 * tells us it's cheaper.  Otherwise, always indexscan if an index is
	 * provided, else plain seqscan.
	 */
	if (OldIndex != NULL && OldIndex->rd_rel->relam == BTREE_AM_OID)
		use_sort = plan_cluster_use_sort(RelationGetRelid(OldHeap),
										 RelationGetRelid(OldIndex));
	else
		use_sort = false;

	/* Log what we're doing */
	if (OldIndex != NULL && !use_sort)
		ereport(elevel,
				errmsg("repacking \"%s.%s\" using index scan on \"%s\"",
					   nspname,
					   RelationGetRelationName(OldHeap),
					   RelationGetRelationName(OldIndex)));
	else if (use_sort)
		ereport(elevel,
				errmsg("repacking \"%s.%s\" using sequential scan and sort",
					   nspname,
					   RelationGetRelationName(OldHeap)));
	else
		ereport(elevel,
				errmsg("repacking \"%s.%s\" in physical order",
					   nspname,
					   RelationGetRelationName(OldHeap)));

	/*
	 * Hand off the actual copying to AM specific function, the generic code
	 * cannot know how to deal with visibility across AMs. Note that this
	 * routine is allowed to set FreezeXid / MultiXactCutoff to different
	 * values (e.g. because the AM doesn't use freezing).
	 */
	table_relation_copy_for_cluster(OldHeap, NewHeap, OldIndex, use_sort,
									cutoffs.OldestXmin, &cutoffs.FreezeLimit,
									&cutoffs.MultiXactCutoff,
									&num_tuples, &tups_vacuumed,
									&tups_recently_dead);

	/* return selected values to caller, get set as relfrozenxid/minmxid */
	*pFreezeXid = cutoffs.FreezeLimit;
	*pCutoffMulti = cutoffs.MultiXactCutoff;

	/* Reset rd_toastoid just to be tidy --- it shouldn't be looked at again */
	NewHeap->rd_toastoid = InvalidOid;

	num_pages = RelationGetNumberOfBlocks(NewHeap);

	/* Log what we did */
	ereport(elevel,
			(errmsg("\"%s.%s\": found %.0f removable, %.0f nonremovable row versions in %u pages",
					nspname,
					RelationGetRelationName(OldHeap),
					tups_vacuumed, num_tuples,
					RelationGetNumberOfBlocks(OldHeap)),
			 errdetail("%.0f dead row versions cannot be removed yet.\n"
					   "%s.",
					   tups_recently_dead,
					   pg_rusage_show(&ru0))));

	/* Update pg_class to reflect the correct values of pages and tuples. */
	relRelation = table_open(RelationRelationId, RowExclusiveLock);

	reltup = SearchSysCacheCopy1(RELOID,
								 ObjectIdGetDatum(RelationGetRelid(NewHeap)));
	if (!HeapTupleIsValid(reltup))
		elog(ERROR, "cache lookup failed for relation %u",
			 RelationGetRelid(NewHeap));
	relform = (Form_pg_class) GETSTRUCT(reltup);

	relform->relpages = num_pages;
	relform->reltuples = num_tuples;

	/* Don't update the stats for pg_class.  See swap_relation_files. */
	if (RelationGetRelid(OldHeap) != RelationRelationId)
		CatalogTupleUpdate(relRelation, &reltup->t_self, reltup);
	else
		CacheInvalidateRelcacheByTuple(reltup);

	/* Clean up. */
	heap_freetuple(reltup);
	table_close(relRelation, RowExclusiveLock);

	/* Make the update visible */
	CommandCounterIncrement();
}

/*
 * Swap the physical files of two given relations.
 *
 * We swap the physical identity (reltablespace, relfilenumber) while keeping
 * the same logical identities of the two relations.  relpersistence is also
 * swapped, which is critical since it determines where buffers live for each
 * relation.
 *
 * We can swap associated TOAST data in either of two ways: recursively swap
 * the physical content of the toast tables (and their indexes), or swap the
 * TOAST links in the given relations' pg_class entries.  The former is needed
 * to manage rewrites of shared catalogs (where we cannot change the pg_class
 * links) while the latter is the only way to handle cases in which a toast
 * table is added or removed altogether.
 *
 * Additionally, the first relation is marked with relfrozenxid set to
 * frozenXid.  It seems a bit ugly to have this here, but the caller would
 * have to do it anyway, so having it here saves a heap_update.  Note: in
 * the swap-toast-links case, we assume we don't need to change the toast
 * table's relfrozenxid: the new version of the toast table should already
 * have relfrozenxid set to RecentXmin, which is good enough.
 *
 * Lastly, if r2 and its toast table and toast index (if any) are mapped,
 * their OIDs are emitted into mapped_tables[].  This is hacky but beats
 * having to look the information up again later in finish_heap_swap.
 */
static void
swap_relation_files(Oid r1, Oid r2, bool target_is_pg_class,
					bool swap_toast_by_content,
					bool is_internal,
					TransactionId frozenXid,
					MultiXactId cutoffMulti,
					Oid *mapped_tables)
{
	Relation	relRelation;
	HeapTuple	reltup1,
				reltup2;
	Form_pg_class relform1,
				relform2;
	RelFileNumber relfilenumber1,
				relfilenumber2;
	RelFileNumber swaptemp;
	char		swptmpchr;
	Oid			relam1,
				relam2;

	/* We need writable copies of both pg_class tuples. */
	relRelation = table_open(RelationRelationId, RowExclusiveLock);

	reltup1 = SearchSysCacheCopy1(RELOID, ObjectIdGetDatum(r1));
	if (!HeapTupleIsValid(reltup1))
		elog(ERROR, "cache lookup failed for relation %u", r1);
	relform1 = (Form_pg_class) GETSTRUCT(reltup1);

	reltup2 = SearchSysCacheCopy1(RELOID, ObjectIdGetDatum(r2));
	if (!HeapTupleIsValid(reltup2))
		elog(ERROR, "cache lookup failed for relation %u", r2);
	relform2 = (Form_pg_class) GETSTRUCT(reltup2);

	relfilenumber1 = relform1->relfilenode;
	relfilenumber2 = relform2->relfilenode;
	relam1 = relform1->relam;
	relam2 = relform2->relam;

	if (RelFileNumberIsValid(relfilenumber1) &&
		RelFileNumberIsValid(relfilenumber2))
	{
		/*
		 * Normal non-mapped relations: swap relfilenumbers, reltablespaces,
		 * relpersistence
		 */
		Assert(!target_is_pg_class);

		swaptemp = relform1->relfilenode;
		relform1->relfilenode = relform2->relfilenode;
		relform2->relfilenode = swaptemp;

		swaptemp = relform1->reltablespace;
		relform1->reltablespace = relform2->reltablespace;
		relform2->reltablespace = swaptemp;

		swaptemp = relform1->relam;
		relform1->relam = relform2->relam;
		relform2->relam = swaptemp;

		swptmpchr = relform1->relpersistence;
		relform1->relpersistence = relform2->relpersistence;
		relform2->relpersistence = swptmpchr;

		/* Also swap toast links, if we're swapping by links */
		if (!swap_toast_by_content)
		{
			swaptemp = relform1->reltoastrelid;
			relform1->reltoastrelid = relform2->reltoastrelid;
			relform2->reltoastrelid = swaptemp;
		}
	}
	else
	{
		/*
		 * Mapped-relation case.  Here we have to swap the relation mappings
		 * instead of modifying the pg_class columns.  Both must be mapped.
		 */
		if (RelFileNumberIsValid(relfilenumber1) ||
			RelFileNumberIsValid(relfilenumber2))
			elog(ERROR, "cannot swap mapped relation \"%s\" with non-mapped relation",
				 NameStr(relform1->relname));

		/*
		 * We can't change the tablespace nor persistence of a mapped rel, and
		 * we can't handle toast link swapping for one either, because we must
		 * not apply any critical changes to its pg_class row.  These cases
		 * should be prevented by upstream permissions tests, so these checks
		 * are non-user-facing emergency backstop.
		 */
		if (relform1->reltablespace != relform2->reltablespace)
			elog(ERROR, "cannot change tablespace of mapped relation \"%s\"",
				 NameStr(relform1->relname));
		if (relform1->relpersistence != relform2->relpersistence)
			elog(ERROR, "cannot change persistence of mapped relation \"%s\"",
				 NameStr(relform1->relname));
		if (relform1->relam != relform2->relam)
			elog(ERROR, "cannot change access method of mapped relation \"%s\"",
				 NameStr(relform1->relname));
		if (!swap_toast_by_content &&
			(relform1->reltoastrelid || relform2->reltoastrelid))
			elog(ERROR, "cannot swap toast by links for mapped relation \"%s\"",
				 NameStr(relform1->relname));

		/*
		 * Fetch the mappings --- shouldn't fail, but be paranoid
		 */
		relfilenumber1 = RelationMapOidToFilenumber(r1, relform1->relisshared);
		if (!RelFileNumberIsValid(relfilenumber1))
			elog(ERROR, "could not find relation mapping for relation \"%s\", OID %u",
				 NameStr(relform1->relname), r1);
		relfilenumber2 = RelationMapOidToFilenumber(r2, relform2->relisshared);
		if (!RelFileNumberIsValid(relfilenumber2))
			elog(ERROR, "could not find relation mapping for relation \"%s\", OID %u",
				 NameStr(relform2->relname), r2);

		/*
		 * Send replacement mappings to relmapper.  Note these won't actually
		 * take effect until CommandCounterIncrement.
		 */
		RelationMapUpdateMap(r1, relfilenumber2, relform1->relisshared, false);
		RelationMapUpdateMap(r2, relfilenumber1, relform2->relisshared, false);

		/* Pass OIDs of mapped r2 tables back to caller */
		*mapped_tables++ = r2;
	}

	/*
	 * Recognize that rel1's relfilenumber (swapped from rel2) is new in this
	 * subtransaction. The rel2 storage (swapped from rel1) may or may not be
	 * new.
	 */
	{
		Relation	rel1,
					rel2;

		rel1 = relation_open(r1, NoLock);
		rel2 = relation_open(r2, NoLock);
		rel2->rd_createSubid = rel1->rd_createSubid;
		rel2->rd_newRelfilelocatorSubid = rel1->rd_newRelfilelocatorSubid;
		rel2->rd_firstRelfilelocatorSubid = rel1->rd_firstRelfilelocatorSubid;
		RelationAssumeNewRelfilelocator(rel1);
		relation_close(rel1, NoLock);
		relation_close(rel2, NoLock);
	}

	/*
	 * In the case of a shared catalog, these next few steps will only affect
	 * our own database's pg_class row; but that's okay, because they are all
	 * noncritical updates.  That's also an important fact for the case of a
	 * mapped catalog, because it's possible that we'll commit the map change
	 * and then fail to commit the pg_class update.
	 */

	/* set rel1's frozen Xid and minimum MultiXid */
	if (relform1->relkind != RELKIND_INDEX)
	{
		Assert(!TransactionIdIsValid(frozenXid) ||
			   TransactionIdIsNormal(frozenXid));
		relform1->relfrozenxid = frozenXid;
		relform1->relminmxid = cutoffMulti;
	}

	/* swap size statistics too, since new rel has freshly-updated stats */
	{
		int32		swap_pages;
		float4		swap_tuples;
		int32		swap_allvisible;
		int32		swap_allfrozen;

		swap_pages = relform1->relpages;
		relform1->relpages = relform2->relpages;
		relform2->relpages = swap_pages;

		swap_tuples = relform1->reltuples;
		relform1->reltuples = relform2->reltuples;
		relform2->reltuples = swap_tuples;

		swap_allvisible = relform1->relallvisible;
		relform1->relallvisible = relform2->relallvisible;
		relform2->relallvisible = swap_allvisible;

		swap_allfrozen = relform1->relallfrozen;
		relform1->relallfrozen = relform2->relallfrozen;
		relform2->relallfrozen = swap_allfrozen;
	}

	/*
	 * Update the tuples in pg_class --- unless the target relation of the
	 * swap is pg_class itself.  In that case, there is zero point in making
	 * changes because we'd be updating the old data that we're about to throw
	 * away.  Because the real work being done here for a mapped relation is
	 * just to change the relation map settings, it's all right to not update
	 * the pg_class rows in this case. The most important changes will instead
	 * performed later, in finish_heap_swap() itself.
	 */
	if (!target_is_pg_class)
	{
		CatalogIndexState indstate;

		indstate = CatalogOpenIndexes(relRelation);
		CatalogTupleUpdateWithInfo(relRelation, &reltup1->t_self, reltup1,
								   indstate);
		CatalogTupleUpdateWithInfo(relRelation, &reltup2->t_self, reltup2,
								   indstate);
		CatalogCloseIndexes(indstate);
	}
	else
	{
		/* no update ... but we do still need relcache inval */
		CacheInvalidateRelcacheByTuple(reltup1);
		CacheInvalidateRelcacheByTuple(reltup2);
	}

	/*
	 * Now that pg_class has been updated with its relevant information for
	 * the swap, update the dependency of the relations to point to their new
	 * table AM, if it has changed.
	 */
	if (relam1 != relam2)
	{
		if (changeDependencyFor(RelationRelationId,
								r1,
								AccessMethodRelationId,
								relam1,
								relam2) != 1)
			elog(ERROR, "could not change access method dependency for relation \"%s.%s\"",
				 get_namespace_name(get_rel_namespace(r1)),
				 get_rel_name(r1));
		if (changeDependencyFor(RelationRelationId,
								r2,
								AccessMethodRelationId,
								relam2,
								relam1) != 1)
			elog(ERROR, "could not change access method dependency for relation \"%s.%s\"",
				 get_namespace_name(get_rel_namespace(r2)),
				 get_rel_name(r2));
	}

	/*
	 * Post alter hook for modified relations. The change to r2 is always
	 * internal, but r1 depends on the invocation context.
	 */
	InvokeObjectPostAlterHookArg(RelationRelationId, r1, 0,
								 InvalidOid, is_internal);
	InvokeObjectPostAlterHookArg(RelationRelationId, r2, 0,
								 InvalidOid, true);

	/*
	 * If we have toast tables associated with the relations being swapped,
	 * deal with them too.
	 */
	if (relform1->reltoastrelid || relform2->reltoastrelid)
	{
		if (swap_toast_by_content)
		{
			if (relform1->reltoastrelid && relform2->reltoastrelid)
			{
				/* Recursively swap the contents of the toast tables */
				swap_relation_files(relform1->reltoastrelid,
									relform2->reltoastrelid,
									target_is_pg_class,
									swap_toast_by_content,
									is_internal,
									frozenXid,
									cutoffMulti,
									mapped_tables);
			}
			else
			{
				/* caller messed up */
				elog(ERROR, "cannot swap toast files by content when there's only one");
			}
		}
		else
		{
			/*
			 * We swapped the ownership links, so we need to change dependency
			 * data to match.
			 *
			 * NOTE: it is possible that only one table has a toast table.
			 *
			 * NOTE: at present, a TOAST table's only dependency is the one on
			 * its owning table.  If more are ever created, we'd need to use
			 * something more selective than deleteDependencyRecordsFor() to
			 * get rid of just the link we want.
			 */
			ObjectAddress baseobject,
						toastobject;
			long		count;

			/*
			 * We disallow this case for system catalogs, to avoid the
			 * possibility that the catalog we're rebuilding is one of the
			 * ones the dependency changes would change.  It's too late to be
			 * making any data changes to the target catalog.
			 */
			if (IsSystemClass(r1, relform1))
				elog(ERROR, "cannot swap toast files by links for system catalogs");

			/* Delete old dependencies */
			if (relform1->reltoastrelid)
			{
				count = deleteDependencyRecordsFor(RelationRelationId,
												   relform1->reltoastrelid,
												   false);
				if (count != 1)
					elog(ERROR, "expected one dependency record for TOAST table, found %ld",
						 count);
			}
			if (relform2->reltoastrelid)
			{
				count = deleteDependencyRecordsFor(RelationRelationId,
												   relform2->reltoastrelid,
												   false);
				if (count != 1)
					elog(ERROR, "expected one dependency record for TOAST table, found %ld",
						 count);
			}

			/* Register new dependencies */
			baseobject.classId = RelationRelationId;
			baseobject.objectSubId = 0;
			toastobject.classId = RelationRelationId;
			toastobject.objectSubId = 0;

			if (relform1->reltoastrelid)
			{
				baseobject.objectId = r1;
				toastobject.objectId = relform1->reltoastrelid;
				recordDependencyOn(&toastobject, &baseobject,
								   DEPENDENCY_INTERNAL);
			}

			if (relform2->reltoastrelid)
			{
				baseobject.objectId = r2;
				toastobject.objectId = relform2->reltoastrelid;
				recordDependencyOn(&toastobject, &baseobject,
								   DEPENDENCY_INTERNAL);
			}
		}
	}

	/*
	 * If we're swapping two toast tables by content, do the same for their
	 * valid index. The swap can actually be safely done only if the relations
	 * have indexes.
	 */
	if (swap_toast_by_content &&
		relform1->relkind == RELKIND_TOASTVALUE &&
		relform2->relkind == RELKIND_TOASTVALUE)
	{
		Oid			toastIndex1,
					toastIndex2;

		/* Get valid index for each relation */
		toastIndex1 = toast_get_valid_index(r1,
											AccessExclusiveLock);
		toastIndex2 = toast_get_valid_index(r2,
											AccessExclusiveLock);

		swap_relation_files(toastIndex1,
							toastIndex2,
							target_is_pg_class,
							swap_toast_by_content,
							is_internal,
							InvalidTransactionId,
							InvalidMultiXactId,
							mapped_tables);
	}

	/* Clean up. */
	heap_freetuple(reltup1);
	heap_freetuple(reltup2);

	table_close(relRelation, RowExclusiveLock);
}

/*
 * Remove the transient table that was built by make_new_heap, and finish
 * cleaning up (including rebuilding all indexes on the old heap).
 */
void
finish_heap_swap(Oid OIDOldHeap, Oid OIDNewHeap,
				 bool is_system_catalog,
				 bool swap_toast_by_content,
				 bool check_constraints,
				 bool is_internal,
				 TransactionId frozenXid,
				 MultiXactId cutoffMulti,
				 char newrelpersistence)
{
	ObjectAddress object;
	Oid			mapped_tables[4];
	int			reindex_flags;
	ReindexParams reindex_params = {0};
	int			i;

	/* Report that we are now swapping relation files */
	pgstat_progress_update_param(PROGRESS_REPACK_PHASE,
								 PROGRESS_REPACK_PHASE_SWAP_REL_FILES);

	/* Zero out possible results from swapped_relation_files */
	memset(mapped_tables, 0, sizeof(mapped_tables));

	/*
	 * Swap the contents of the heap relations (including any toast tables).
	 * Also set old heap's relfrozenxid to frozenXid.
	 */
	swap_relation_files(OIDOldHeap, OIDNewHeap,
						(OIDOldHeap == RelationRelationId),
						swap_toast_by_content, is_internal,
						frozenXid, cutoffMulti, mapped_tables);

	/*
	 * If it's a system catalog, queue a sinval message to flush all catcaches
	 * on the catalog when we reach CommandCounterIncrement.
	 */
	if (is_system_catalog)
		CacheInvalidateCatalog(OIDOldHeap);

	/*
	 * Rebuild each index on the relation (but not the toast table, which is
	 * all-new at this point).  It is important to do this before the DROP
	 * step because if we are processing a system catalog that will be used
	 * during DROP, we want to have its indexes available.  There is no
	 * advantage to the other order anyway because this is all transactional,
	 * so no chance to reclaim disk space before commit.  We do not need a
	 * final CommandCounterIncrement() because reindex_relation does it.
	 *
	 * Note: because index_build is called via reindex_relation, it will never
	 * set indcheckxmin true for the indexes.  This is OK even though in some
	 * sense we are building new indexes rather than rebuilding existing ones,
	 * because the new heap won't contain any HOT chains at all, let alone
	 * broken ones, so it can't be necessary to set indcheckxmin.
	 */
	reindex_flags = REINDEX_REL_SUPPRESS_INDEX_USE;
	if (check_constraints)
		reindex_flags |= REINDEX_REL_CHECK_CONSTRAINTS;

	/*
	 * Ensure that the indexes have the same persistence as the parent
	 * relation.
	 */
	if (newrelpersistence == RELPERSISTENCE_UNLOGGED)
		reindex_flags |= REINDEX_REL_FORCE_INDEXES_UNLOGGED;
	else if (newrelpersistence == RELPERSISTENCE_PERMANENT)
		reindex_flags |= REINDEX_REL_FORCE_INDEXES_PERMANENT;

	/* Report that we are now reindexing relations */
	pgstat_progress_update_param(PROGRESS_REPACK_PHASE,
								 PROGRESS_REPACK_PHASE_REBUILD_INDEX);

	reindex_relation(NULL, OIDOldHeap, reindex_flags, &reindex_params);

	/* Report that we are now doing clean up */
	pgstat_progress_update_param(PROGRESS_REPACK_PHASE,
								 PROGRESS_REPACK_PHASE_FINAL_CLEANUP);

	/*
	 * If the relation being rebuilt is pg_class, swap_relation_files()
	 * couldn't update pg_class's own pg_class entry (check comments in
	 * swap_relation_files()), thus relfrozenxid was not updated. That's
	 * annoying because a potential reason for doing a VACUUM FULL is a
	 * imminent or actual anti-wraparound shutdown.  So, now that we can
	 * access the new relation using its indices, update relfrozenxid.
	 * pg_class doesn't have a toast relation, so we don't need to update the
	 * corresponding toast relation. Not that there's little point moving all
	 * relfrozenxid updates here since swap_relation_files() needs to write to
	 * pg_class for non-mapped relations anyway.
	 */
	if (OIDOldHeap == RelationRelationId)
	{
		Relation	relRelation;
		HeapTuple	reltup;
		Form_pg_class relform;

		relRelation = table_open(RelationRelationId, RowExclusiveLock);

		reltup = SearchSysCacheCopy1(RELOID, ObjectIdGetDatum(OIDOldHeap));
		if (!HeapTupleIsValid(reltup))
			elog(ERROR, "cache lookup failed for relation %u", OIDOldHeap);
		relform = (Form_pg_class) GETSTRUCT(reltup);

		relform->relfrozenxid = frozenXid;
		relform->relminmxid = cutoffMulti;

		CatalogTupleUpdate(relRelation, &reltup->t_self, reltup);

		table_close(relRelation, RowExclusiveLock);
	}

	/* Destroy new heap with old filenumber */
	object.classId = RelationRelationId;
	object.objectId = OIDNewHeap;
	object.objectSubId = 0;

	/*
	 * The new relation is local to our transaction and we know nothing
	 * depends on it, so DROP_RESTRICT should be OK.
	 */
	performDeletion(&object, DROP_RESTRICT, PERFORM_DELETION_INTERNAL);

	/* performDeletion does CommandCounterIncrement at end */

	/*
	 * Now we must remove any relation mapping entries that we set up for the
	 * transient table, as well as its toast table and toast index if any. If
	 * we fail to do this before commit, the relmapper will complain about new
	 * permanent map entries being added post-bootstrap.
	 */
	for (i = 0; OidIsValid(mapped_tables[i]); i++)
		RelationMapRemoveMapping(mapped_tables[i]);

	/*
	 * At this point, everything is kosher except that, if we did toast swap
	 * by links, the toast table's name corresponds to the transient table.
	 * The name is irrelevant to the backend because it's referenced by OID,
	 * but users looking at the catalogs could be confused.  Rename it to
	 * prevent this problem.
	 *
	 * Note no lock required on the relation, because we already hold an
	 * exclusive lock on it.
	 */
	if (!swap_toast_by_content)
	{
		Relation	newrel;

		newrel = table_open(OIDOldHeap, NoLock);
		if (OidIsValid(newrel->rd_rel->reltoastrelid))
		{
			Oid			toastidx;
			char		NewToastName[NAMEDATALEN];

			/* Get the associated valid index to be renamed */
			toastidx = toast_get_valid_index(newrel->rd_rel->reltoastrelid,
											 NoLock);

			/* rename the toast table ... */
			snprintf(NewToastName, NAMEDATALEN, "pg_toast_%u",
					 OIDOldHeap);
			RenameRelationInternal(newrel->rd_rel->reltoastrelid,
								   NewToastName, true, false);

			/* ... and its valid index too. */
			snprintf(NewToastName, NAMEDATALEN, "pg_toast_%u_index",
					 OIDOldHeap);

			RenameRelationInternal(toastidx,
								   NewToastName, true, true);

			/*
			 * Reset the relrewrite for the toast. The command-counter
			 * increment is required here as we are about to update the tuple
			 * that is updated as part of RenameRelationInternal.
			 */
			CommandCounterIncrement();
			ResetRelRewrite(newrel->rd_rel->reltoastrelid);
		}
		relation_close(newrel, NoLock);
	}

	/* if it's not a catalog table, clear any missing attribute settings */
	if (!is_system_catalog)
	{
		Relation	newrel;

		newrel = table_open(OIDOldHeap, NoLock);
		RelationClearMissing(newrel);
		relation_close(newrel, NoLock);
	}
}

/*
 * Determine which relations to process, when REPACK/CLUSTER is called
 * without specifying a table name.  The exact process depends on whether
 * USING INDEX was given or not, and in any case we only return tables and
 * materialized views that the current user has privileges to repack/cluster.
 *
 * If USING INDEX was given, we scan pg_index to find those that have
 * indisclustered set; if it was not given, scan pg_class and return all
 * tables.
 *
 * Return it as a list of RelToCluster in the given memory context.
 */
static List *
get_tables_to_repack(RepackCommand cmd, bool usingindex, MemoryContext permcxt)
{
	Relation	catalog;
	TableScanDesc scan;
	HeapTuple	tuple;
	List	   *rtcs = NIL;

	if (usingindex)
	{
		ScanKeyData entry;

		/*
		 * For USING INDEX, scan pg_index to find those with indisclustered.
		 */
		catalog = table_open(IndexRelationId, AccessShareLock);
		ScanKeyInit(&entry,
					Anum_pg_index_indisclustered,
					BTEqualStrategyNumber, F_BOOLEQ,
					BoolGetDatum(true));
		scan = table_beginscan_catalog(catalog, 1, &entry);
		while ((tuple = heap_getnext(scan, ForwardScanDirection)) != NULL)
		{
			RelToCluster *rtc;
			Form_pg_index index;
			MemoryContext oldcxt;

			index = (Form_pg_index) GETSTRUCT(tuple);

			/*
			 * Try to obtain a light lock on the index's table, to ensure it
			 * doesn't go away while we collect the list.  If we cannot, just
			 * disregard it.  Be sure to release this if we ultimately decide
			 * not to process the table!
			 */
			if (!ConditionalLockRelationOid(index->indrelid, AccessShareLock))
				continue;

			/* Verify that the table still exists; skip if not */
			if (!SearchSysCacheExists1(RELOID, ObjectIdGetDatum(index->indrelid)))
			{
				UnlockRelationOid(index->indrelid, AccessShareLock);
				continue;
			}

			/* noisily skip rels which the user can't process */
			if (!repack_is_permitted_for_relation(cmd, index->indrelid,
												  GetUserId()))
			{
				UnlockRelationOid(index->indrelid, AccessShareLock);
				continue;
			}

			/* Use a permanent memory context for the result list */
			oldcxt = MemoryContextSwitchTo(permcxt);
			rtc = palloc_object(RelToCluster);
			rtc->tableOid = index->indrelid;
			rtc->indexOid = index->indexrelid;
			rtcs = lappend(rtcs, rtc);
			MemoryContextSwitchTo(oldcxt);
		}
	}
	else
	{
		catalog = table_open(RelationRelationId, AccessShareLock);
		scan = table_beginscan_catalog(catalog, 0, NULL);

		while ((tuple = heap_getnext(scan, ForwardScanDirection)) != NULL)
		{
			RelToCluster *rtc;
			Form_pg_class class;
			MemoryContext oldcxt;

			class = (Form_pg_class) GETSTRUCT(tuple);

			/*
			 * Try to obtain a light lock on the table, to ensure it doesn't
			 * go away while we collect the list.  If we cannot, just
			 * disregard the table.  Be sure to release this if we ultimately
			 * decide not to process the table!
			 */
			if (!ConditionalLockRelationOid(class->oid, AccessShareLock))
				continue;

			/* Verify that the table still exists */
			if (!SearchSysCacheExists1(RELOID, ObjectIdGetDatum(class->oid)))
			{
				UnlockRelationOid(class->oid, AccessShareLock);
				continue;
			}

			/* Can only process plain tables and matviews */
			if (class->relkind != RELKIND_RELATION &&
				class->relkind != RELKIND_MATVIEW)
			{
				UnlockRelationOid(class->oid, AccessShareLock);
				continue;
			}

			/* noisily skip rels which the user can't process */
			if (!repack_is_permitted_for_relation(cmd, class->oid,
												  GetUserId()))
			{
				UnlockRelationOid(class->oid, AccessShareLock);
				continue;
			}

			/* Use a permanent memory context for the result list */
			oldcxt = MemoryContextSwitchTo(permcxt);
			rtc = palloc_object(RelToCluster);
			rtc->tableOid = class->oid;
			rtc->indexOid = InvalidOid;
			rtcs = lappend(rtcs, rtc);
			MemoryContextSwitchTo(oldcxt);
		}
	}

	table_endscan(scan);
	relation_close(catalog, AccessShareLock);

	return rtcs;
}

/*
 * Given a partitioned table or its index, return a list of RelToCluster for
 * all the leaf child tables/indexes.
 *
 * 'rel_is_index' tells whether 'relid' is that of an index (true) or of the
 * owning relation.
 */
static List *
get_tables_to_repack_partitioned(RepackCommand cmd, Oid relid,
								 bool rel_is_index, MemoryContext permcxt)
{
	List	   *inhoids;
	List	   *rtcs = NIL;

	/*
	 * Do not lock the children until they're processed.  Note that we do hold
	 * a lock on the parent partitioned table.
	 */
	inhoids = find_all_inheritors(relid, NoLock, NULL);
	foreach_oid(child_oid, inhoids)
	{
		Oid			table_oid,
					index_oid;
		RelToCluster *rtc;
		MemoryContext oldcxt;

		if (rel_is_index)
		{
			/* consider only leaf indexes */
			if (get_rel_relkind(child_oid) != RELKIND_INDEX)
				continue;

			table_oid = IndexGetRelation(child_oid, false);
			index_oid = child_oid;
		}
		else
		{
			/* consider only leaf relations */
			if (get_rel_relkind(child_oid) != RELKIND_RELATION)
				continue;

			table_oid = child_oid;
			index_oid = InvalidOid;
		}

		/*
		 * It's possible that the user does not have privileges to CLUSTER the
		 * leaf partition despite having them on the partitioned table.  Skip
		 * if so.
		 */
		if (!repack_is_permitted_for_relation(cmd, table_oid, GetUserId()))
			continue;

		/* Use a permanent memory context for the result list */
		oldcxt = MemoryContextSwitchTo(permcxt);
		rtc = palloc_object(RelToCluster);
		rtc->tableOid = table_oid;
		rtc->indexOid = index_oid;
		rtcs = lappend(rtcs, rtc);
		MemoryContextSwitchTo(oldcxt);
	}

	return rtcs;
}


/*
 * Return whether userid has privileges to REPACK relid.  If not, this
 * function emits a WARNING.
 */
static bool
repack_is_permitted_for_relation(RepackCommand cmd, Oid relid, Oid userid)
{
	Assert(cmd == REPACK_COMMAND_CLUSTER || cmd == REPACK_COMMAND_REPACK);

	if (pg_class_aclcheck(relid, userid, ACL_MAINTAIN) == ACLCHECK_OK)
		return true;

	ereport(WARNING,
			errmsg("permission denied to execute %s on \"%s\", skipping it",
				   RepackCommandAsString(cmd),
				   get_rel_name(relid)));

	return false;
}


/*
 * Given a RepackStmt with an indicated relation name, resolve the relation
 * name, obtain lock on it, then determine what to do based on the relation
 * type: if it's table and not partitioned, repack it as indicated (using an
 * existing clustered index, or following the given one), and return NULL.
 *
 * On the other hand, if the table is partitioned, do nothing further and
 * instead return the opened and locked relcache entry, so that caller can
 * process the partitions using the multiple-table handling code.  In this
 * case, if an index name is given, it's up to the caller to resolve it.
 */
static Relation
process_single_relation(RepackStmt *stmt, ClusterParams *params)
{
	Relation	rel;
	Oid			tableOid;
	LOCKMODE	lockmode;

	Assert(stmt->relation != NULL);
	Assert(stmt->command == REPACK_COMMAND_CLUSTER ||
		   stmt->command == REPACK_COMMAND_REPACK);

	/*
	 * Make sure ANALYZE is specified if a column list is present.
	 */
	if ((params->options & CLUOPT_ANALYZE) == 0 && stmt->relation->va_cols != NIL)
		ereport(ERROR,
				errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				errmsg("ANALYZE option must be specified when a column list is provided"));

	/*
	 * In concurrent mode, we use ShareUpdateExclusiveLock to allow DML to
	 * proceed during the initial copy phase.  In normal mode, we obtain
	 * AccessExclusiveLock right away to avoid lock-upgrade hazard in the
	 * single-transaction case.
	 */
	lockmode = (params->options & CLUOPT_CONCURRENT) ?
		ShareUpdateExclusiveLock : AccessExclusiveLock;

	tableOid = RangeVarGetRelidExtended(stmt->relation->relation,
										lockmode,
										0,
										RangeVarCallbackMaintainsTable,
										NULL);
	rel = table_open(tableOid, NoLock);

	/*
	 * Reject clustering a remote temp table ... their local buffer manager is
	 * not going to cope.
	 */
	if (RELATION_IS_OTHER_TEMP(rel))
		ereport(ERROR,
				errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
		/*- translator: first %s is name of a SQL command, eg. REPACK */
				errmsg("cannot execute %s on temporary tables of other sessions",
					   RepackCommandAsString(stmt->command)));

	/*
	 * CONCURRENTLY cannot be used on system catalogs or shared relations.
	 */
	if (params->options & CLUOPT_CONCURRENT)
	{
		if (IsCatalogRelation(rel))
			ereport(ERROR,
					errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					errmsg("REPACK CONCURRENTLY cannot be performed on system catalogs"));

		if (rel->rd_rel->relisshared)
			ereport(ERROR,
					errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					errmsg("REPACK CONCURRENTLY cannot be performed on shared relations"));

		/*
		 * Temporary tables cannot be repacked concurrently; they are
		 * session-local and do not have the concurrency concerns that
		 * CONCURRENTLY addresses.
		 */
		if (rel->rd_rel->relpersistence == RELPERSISTENCE_TEMP)
			ereport(ERROR,
					errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					errmsg("REPACK CONCURRENTLY cannot be performed on temporary tables"));
	}

	/*
	 * For partitioned tables, let caller handle this.  CONCURRENTLY is not
	 * supported for partitioned tables.
	 */
	if (rel->rd_rel->relkind == RELKIND_PARTITIONED_TABLE)
	{
		if (params->options & CLUOPT_CONCURRENT)
			ereport(ERROR,
					errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					errmsg("REPACK CONCURRENTLY cannot be performed on partitioned tables"),
					errhint("Repack each partition individually."));
		return rel;
	}
	else
	{
		Oid			indexOid;

		indexOid = determine_clustered_index(rel, stmt->usingindex,
											 stmt->indexname);

		if (params->options & CLUOPT_CONCURRENT)
		{
			/*
			 * In concurrent mode, we handle the index validity check and then
			 * dispatch to the concurrent repack path.  We close the relation
			 * here since repack_relation_concurrent will manage its own
			 * transaction lifecycle.
			 */
			if (OidIsValid(indexOid))
				check_index_is_clusterable(rel, indexOid, ShareUpdateExclusiveLock);
			table_close(rel, NoLock);
			repack_relation_concurrent(tableOid, indexOid, params);
		}
		else
		{
			if (OidIsValid(indexOid))
				check_index_is_clusterable(rel, indexOid, AccessExclusiveLock);
			cluster_rel(stmt->command, rel, indexOid, params);

			/*
			 * Do an analyze, if requested.  We close the transaction and start a
			 * new one, so that we don't hold the stronger lock for longer than
			 * needed.
			 */
			if (params->options & CLUOPT_ANALYZE)
			{
				VacuumParams vac_params = {0};

				PopActiveSnapshot();
				CommitTransactionCommand();

				StartTransactionCommand();
				PushActiveSnapshot(GetTransactionSnapshot());

				vac_params.options |= VACOPT_ANALYZE;
				if (params->options & CLUOPT_VERBOSE)
					vac_params.options |= VACOPT_VERBOSE;
				analyze_rel(tableOid, NULL, vac_params,
							stmt->relation->va_cols, true, NULL);
				PopActiveSnapshot();
				CommandCounterIncrement();
			}
		}

		return NULL;
	}
}

/*
 * Given a relation and the usingindex/indexname options in a
 * REPACK USING INDEX or CLUSTER command, return the OID of the
 * index to use for clustering the table.
 *
 * Caller must hold lock on the relation so that the set of indexes
 * doesn't change, and must call check_index_is_clusterable.
 */
static Oid
determine_clustered_index(Relation rel, bool usingindex, const char *indexname)
{
	Oid			indexOid;

	if (indexname == NULL && usingindex)
	{
		/*
		 * If USING INDEX with no name is given, find a clustered index, or
		 * error out if none.
		 */
		indexOid = InvalidOid;
		foreach_oid(idxoid, RelationGetIndexList(rel))
		{
			if (get_index_isclustered(idxoid))
			{
				indexOid = idxoid;
				break;
			}
		}

		if (!OidIsValid(indexOid))
			ereport(ERROR,
					errcode(ERRCODE_UNDEFINED_OBJECT),
					errmsg("there is no previously clustered index for table \"%s\"",
						   RelationGetRelationName(rel)));
	}
	else if (indexname != NULL)
	{
		/* An index was specified; obtain its OID. */
		indexOid = get_relname_relid(indexname, rel->rd_rel->relnamespace);
		if (!OidIsValid(indexOid))
			ereport(ERROR,
					errcode(ERRCODE_UNDEFINED_OBJECT),
					errmsg("index \"%s\" for table \"%s\" does not exist",
						   indexname, RelationGetRelationName(rel)));
	}
	else
		indexOid = InvalidOid;

	return indexOid;
}

static const char *
RepackCommandAsString(RepackCommand cmd)
{
	switch (cmd)
	{
		case REPACK_COMMAND_REPACK:
			return "REPACK";
		case REPACK_COMMAND_VACUUMFULL:
			return "VACUUM";
		case REPACK_COMMAND_CLUSTER:
			return "CLUSTER";
	}
	return "???";				/* keep compiler quiet */
}

/*
 * tuples_are_equal
 *
 * Compare two heap tuples attribute by attribute for equality.  Dropped
 * columns are skipped.  NULL values compare equal to NULL; a NULL and a
 * non-NULL value compare unequal.
 *
 * For variable-length attributes, values are detoasted before comparison to
 * correctly handle cases where one copy is stored out-of-line (TOAST pointer)
 * and the other is stored inline — as can happen when comparing old-heap
 * tuples (which may retain TOAST pointers) against Phase-1 new-heap tuples
 * (which had large values inlined by copy_table_data).
 *
 * Uses datumIsEqual() for fixed-length attributes.
 */
static bool
tuples_are_equal(TupleDesc tupdesc, HeapTuple tup1, HeapTuple tup2)
{
	for (int i = 0; i < tupdesc->natts; i++)
	{
		Form_pg_attribute attr = TupleDescAttr(tupdesc, i);
		bool		isnull1,
					isnull2;
		Datum		d1,
					d2;

		/* Skip dropped columns */
		if (attr->attisdropped)
			continue;

		d1 = heap_getattr(tup1, i + 1, tupdesc, &isnull1);
		d2 = heap_getattr(tup2, i + 1, tupdesc, &isnull2);

		if (isnull1 != isnull2)
			return false;

		if (isnull1)
			continue;			/* both NULL, continue */

		if (!attr->attbyval && attr->attlen == -1)
		{
			/*
			 * Variable-length attribute: detoast both values before
			 * comparing so that out-of-line TOAST pointers and inline data
			 * for the same logical value compare as equal.
			 */
			Datum		d1d = PointerGetDatum(PG_DETOAST_DATUM(d1));
			Datum		d2d = PointerGetDatum(PG_DETOAST_DATUM(d2));
			bool		eq = datumIsEqual(d1d, d2d, false, attr->attlen);

			if (DatumGetPointer(d1d) != DatumGetPointer(d1))
				pfree(DatumGetPointer(d1d));
			if (DatumGetPointer(d2d) != DatumGetPointer(d2))
				pfree(DatumGetPointer(d2d));

			if (!eq)
				return false;
		}
		else
		{
			if (!datumIsEqual(d1, d2, attr->attbyval, attr->attlen))
				return false;
		}
	}

	return true;
}

/*
 * repack_relation_concurrent
 *
 * Perform a REPACK CONCURRENTLY operation on a single table.  This function
 * manages its own transaction lifecycle.
 *
 * The algorithm proceeds in three phases:
 *
 * Phase 1 (ShareUpdateExclusiveLock):
 *   Create a new heap and copy all currently visible rows into it.  This
 *   phase allows concurrent DML (INSERT/UPDATE/DELETE) to proceed on the
 *   old table.  We record phase1_snapshot_xmin (the next XID at Phase 1
 *   start) so we can later identify rows that changed after this point.
 *
 * Wait phase:
 *   Wait for any transactions that hold conflicting locks on the old heap
 *   to finish, ensuring that any DML concurrent with Phase 1 has committed
 *   or rolled back before we acquire the exclusive lock in Phase 2.
 *
 * Phase 2 (AccessExclusiveLock):
 *   Apply the delta: insert rows added after Phase 1's snapshot and delete
 *   rows from the new heap that were removed from the old heap after Phase
 *   1's snapshot.  Then swap the physical files of the old and new heaps
 *   and rebuild indexes.
 *
 * Delta handling:
 *   - New inserts (xmin >= phase1_snapshot_xmin, committed): copied to
 *     new heap.
 *   - Phantom deletes (row visible before Phase 1, committed xmax >=
 *     phase1_snapshot_xmin): the corresponding row in new heap is found
 *     via content-based matching and deleted.  This is O(deleted_rows *
 *     new_heap_size) in the worst case; in practice, few rows change
 *     between Phase 1 and Phase 2, so this is fast.
 */
static void
repack_relation_concurrent(Oid tableOid, Oid indexOid, ClusterParams *params)
{
	Oid			OIDNewHeap;
	Relation	OldHeap;
	Relation	NewHeap;
	Relation	index = NULL;
	char		relpersistence;
	bool		is_system_catalog;
	bool		swap_toast_by_content;
	TransactionId frozenXid;
	MultiXactId cutoffMulti;
	TransactionId phase1_snapshot_xmin;
	bool		verbose = ((params->options & CLUOPT_VERBOSE) != 0);
	int			elevel = verbose ? INFO : DEBUG2;
	LOCKTAG		heaplocktag;
	LockRelId	heaplockid;
	MemoryContext private_context;
	MemoryContext oldcontext;
	Oid			accessMethod;
	Oid			tableSpace;

	/*
	 * Create a memory context that will survive forced transaction commits we
	 * do below.  Since it is a child of PortalContext, it will go away
	 * eventually even if we suffer an error.
	 */
	private_context = AllocSetContextCreate(PortalContext,
											"RepackConcurrent",
											ALLOCSET_DEFAULT_SIZES);

	/* -----------------------------------------------------------------------
	 * Phase 1: Copy data with ShareUpdateExclusiveLock
	 * -----------------------------------------------------------------------
	 *
	 * We open the relation with the lock already held (it was obtained in
	 * process_single_relation).  Create the new heap and copy all rows that
	 * are visible now.
	 */

	pgstat_progress_start_command(PROGRESS_COMMAND_REPACK, tableOid);
	pgstat_progress_update_param(PROGRESS_REPACK_COMMAND, REPACK_COMMAND_REPACK);

	OldHeap = table_open(tableOid, NoLock);

	Assert(CheckRelationLockedByMe(OldHeap, ShareUpdateExclusiveLock, false));

	/* Check for user-requested abort. */
	CHECK_FOR_INTERRUPTS();

	/*
	 * Don't process temp tables of other backends.
	 */
	if (RELATION_IS_OTHER_TEMP(OldHeap))
		ereport(ERROR,
				errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				errmsg("cannot execute REPACK CONCURRENTLY on temporary tables of other sessions"));

	/*
	 * Quietly skip unpopulated materialized views -- no data to repack.
	 */
	if (OldHeap->rd_rel->relkind == RELKIND_MATVIEW &&
		!RelationIsPopulated(OldHeap))
	{
		table_close(OldHeap, ShareUpdateExclusiveLock);
		pgstat_progress_end_command();
		MemoryContextDelete(private_context);
		return;
	}

	Assert(OldHeap->rd_rel->relkind == RELKIND_RELATION ||
		   OldHeap->rd_rel->relkind == RELKIND_MATVIEW);

	/* Remember needed info before we start manipulating heaps */
	relpersistence = OldHeap->rd_rel->relpersistence;
	is_system_catalog = IsSystemRelation(OldHeap);
	accessMethod = OldHeap->rd_rel->relam;
	tableSpace = OldHeap->rd_rel->reltablespace;

	/* Save lock information for the wait phase (in stable memory context) */
	oldcontext = MemoryContextSwitchTo(private_context);
	heaplockid = OldHeap->rd_lockInfo.lockRelId;
	MemoryContextSwitchTo(oldcontext);
	SET_LOCKTAG_RELATION(heaplocktag, heaplockid.dbId, heaplockid.relId);

	/* Check heap and index are valid to cluster on */
	if (OidIsValid(indexOid))
	{
		check_index_is_clusterable(OldHeap, indexOid, ShareUpdateExclusiveLock);
		index = index_open(indexOid, NoLock);
		/* mark the index as the one to use for clustering */
		mark_index_clustered(OldHeap, indexOid, true);
	}

	ereport(elevel,
			errmsg("repacking \"%s\" concurrently (Phase 1: copying data)",
				   RelationGetRelationName(OldHeap)));

	/*
	 * Create the transient table that will receive the re-ordered data.
	 *
	 * OldHeap is already locked, so no need to lock it again.  make_new_heap
	 * obtains AccessExclusiveLock on the new heap and its toast table.
	 */
	OIDNewHeap = make_new_heap(tableOid, tableSpace,
							   accessMethod,
							   relpersistence,
							   NoLock);
	Assert(CheckRelationOidLockedByMe(OIDNewHeap, AccessExclusiveLock, false));
	NewHeap = table_open(OIDNewHeap, NoLock);

	/*
	 * Record the next XID before we begin the copy.  Any tuple with a
	 * committed xmin >= phase1_snapshot_xmin was inserted after we started
	 * and is thus not in the new heap.  Similarly, any committed deletion
	 * with xmax >= phase1_snapshot_xmin must be reflected in Phase 2.
	 */
	phase1_snapshot_xmin = ReadNextTransactionId();

	/* Copy the heap data into the new table in the desired order */
	copy_table_data(NewHeap, OldHeap, index, verbose,
					&swap_toast_by_content, &frozenXid, &cutoffMulti);

	/* Close relcache entries, but keep lock until transaction commit */
	table_close(OldHeap, NoLock);
	if (index)
		index_close(index, NoLock);
	table_close(NewHeap, NoLock);

	/*
	 * Get a session-level lock on the heap relation to prevent it from
	 * being dropped between transactions.
	 */
	LockRelationIdForSession(&heaplockid, ShareUpdateExclusiveLock);

	/*
	 * Commit Phase 1.  The ShareUpdateExclusiveLock is released here, but
	 * the session-level lock remains so the relation cannot be dropped.
	 */
	PopActiveSnapshot();
	CommitTransactionCommand();

	/* -----------------------------------------------------------------------
	 * Wait phase
	 * -----------------------------------------------------------------------
	 *
	 * Wait until no running transaction holds a conflicting lock on the
	 * old heap.  This ensures any DML that was concurrent with Phase 1 has
	 * finished before we try to acquire AccessExclusiveLock in Phase 2.
	 */
	StartTransactionCommand();

	ereport(elevel,
			errmsg("repacking \"%s\" concurrently (waiting for concurrent transactions)",
				   get_rel_name(tableOid)));

	WaitForLockers(heaplocktag, ShareUpdateExclusiveLock, true);

	CommitTransactionCommand();

	/* -----------------------------------------------------------------------
	 * Phase 2: Apply delta and swap with AccessExclusiveLock
	 * -----------------------------------------------------------------------
	 *
	 * Acquire an exclusive lock to apply the delta (rows that changed after
	 * Phase 1) and perform the file swap.  With AccessExclusiveLock held,
	 * no concurrent DML can run, so the old heap reflects the final state.
	 */
	StartTransactionCommand();

	OldHeap = try_table_open(tableOid, AccessExclusiveLock);
	if (OldHeap == NULL)
	{
		/*
		 * The table was dropped between Phase 1 and Phase 2.  Clean up and
		 * return without error.
		 */
		ereport(WARNING,
				errmsg("table \"%s\" was dropped before REPACK CONCURRENTLY could complete",
					   get_rel_name(tableOid)));
		UnlockRelationIdForSession(&heaplockid, ShareUpdateExclusiveLock);
		pgstat_progress_end_command();
		CommitTransactionCommand();
		MemoryContextDelete(private_context);
		return;
	}

	PushActiveSnapshot(GetTransactionSnapshot());

	ereport(elevel,
			errmsg("repacking \"%s\" concurrently (Phase 2: applying delta)",
				   RelationGetRelationName(OldHeap)));

	/* Reopen the new heap (Phase 1's copy) */
	NewHeap = table_open(OIDNewHeap, AccessExclusiveLock);

	/*
	 * Apply the delta.
	 *
	 * Step 1: Insert rows that were added to the old heap after Phase 1.
	 * These are live rows (visible to the current snapshot) whose xmin >=
	 * phase1_snapshot_xmin.
	 */
	{
		TableScanDesc scan;
		HeapTuple	tuple;
		Snapshot	snap = GetActiveSnapshot();

		scan = table_beginscan(OldHeap, snap, 0, NULL);
		while ((tuple = heap_getnext(scan, ForwardScanDirection)) != NULL)
		{
			TransactionId xmin = HeapTupleHeaderGetRawXmin(tuple->t_data);

			/*
			 * Only process normal XIDs.  FrozenTransactionId and other
			 * special values are always "old" (before Phase 1).
			 * TransactionIdFollowsOrEquals handles non-normal XIDs safely,
			 * but being explicit makes the intent clearer.
			 */
			if (!TransactionIdIsNormal(xmin))
				continue;

			if (!TransactionIdFollowsOrEquals(xmin, phase1_snapshot_xmin))
				continue;		/* row existed before Phase 1, already in new heap */

			/* This row was inserted after Phase 1; copy it to the new heap */
			{
				HeapTuple	newTuple = heap_copytuple(tuple);

				simple_heap_insert(NewHeap, newTuple);
				heap_freetuple(newTuple);
			}

			CHECK_FOR_INTERRUPTS();
		}
		table_endscan(scan);
	}

	/*
	 * Step 2: Remove rows from the new heap that were deleted from the old
	 * heap after Phase 1.  These are rows that:
	 *   (a) were committed before Phase 1 (their xmin < phase1_snapshot_xmin),
	 *       so they appear in Phase 1's new heap copy, and
	 *   (b) had a committed deletion (xmax >= phase1_snapshot_xmin) after
	 *       Phase 1 started, so they should NOT be in the final heap.
	 *
	 * For each such "phantom deleted" row we scan the new heap to find the
	 * corresponding row by content equality, then delete it.  This is
	 * O(phantom_deletes * new_heap_size) but is fast in practice because
	 * few rows change between Phase 1 and Phase 2.
	 */
	{
		TableScanDesc oldscan;
		HeapTuple	oldtuple;
		TupleDesc	tupdesc = RelationGetDescr(OldHeap);

		oldscan = table_beginscan(OldHeap, SnapshotAny, 0, NULL);
		while ((oldtuple = heap_getnext(oldscan, ForwardScanDirection)) != NULL)
		{
			TransactionId xmin = HeapTupleHeaderGetRawXmin(oldtuple->t_data);
			TransactionId xmax = HeapTupleHeaderGetRawXmax(oldtuple->t_data);

			/*
			 * Skip rows not committed before Phase 1:
			 *   - Frozen XIDs (FrozenTransactionId / BootstrapTransactionId)
			 *     are always "before Phase 1" and need no special check.
			 *   - Normal XIDs >= phase1_snapshot_xmin were inserted after
			 *     Phase 1 and are not in the new heap.
			 *   - Non-committed XIDs: row was never inserted; skip.
			 */
			if (TransactionIdIsNormal(xmin))
			{
				if (TransactionIdFollowsOrEquals(xmin, phase1_snapshot_xmin))
					continue;	/* inserted after Phase 1, not in new heap */
				if (!TransactionIdDidCommit(xmin))
					continue;	/* insertion was rolled back; skip */
			}
			else if (!TransactionIdIsValid(xmin))
				continue;		/* invalid xmin; skip */
			/* else: frozen/bootstrap XID, always committed before Phase 1 */

			/*
			 * Now check whether this row was deleted after Phase 1.
			 */
			if (!TransactionIdIsValid(xmax))
				continue;		/* no deletion; row is still live */

			if (!TransactionIdIsNormal(xmax))
				continue;		/* special xmax value; skip */

			if (!TransactionIdFollowsOrEquals(xmax, phase1_snapshot_xmin))
				continue;		/* deleted before Phase 1; already absent from new heap */

			if (!TransactionIdDidCommit(xmax))
				continue;		/* deletion was rolled back; skip */

			/*
			 * This row was committed before Phase 1 (so it is in the new
			 * heap) and was deleted after Phase 1 started.  Find and delete
			 * the matching row in the new heap by content equality.
			 */
			{
				TableScanDesc newscan;
				HeapTuple	newtuple;
				bool		found = false;

				newscan = table_beginscan(NewHeap, SnapshotAny, 0, NULL);
				while ((newtuple = heap_getnext(newscan, ForwardScanDirection)) != NULL)
				{
					/*
					 * Skip already-deleted tuples in the new heap (those
					 * with a valid xmax set by earlier iterations of this
					 * loop).
					 */
					if (TransactionIdIsValid(
							HeapTupleHeaderGetRawXmax(newtuple->t_data)))
						continue;

					if (tuples_are_equal(tupdesc, oldtuple, newtuple))
					{
						simple_heap_delete(NewHeap, &newtuple->t_self);
						found = true;
						break;
					}
				}
				table_endscan(newscan);

				if (!found)
					ereport(DEBUG1,
							errmsg("REPACK CONCURRENTLY: no matching row found in new heap for deleted tuple in \"%s\"",
								   RelationGetRelationName(OldHeap)));
			}

			CHECK_FOR_INTERRUPTS();
		}
		table_endscan(oldscan);
	}

	/* Close relcache entries, but keep lock until transaction commit */
	table_close(OldHeap, NoLock);
	table_close(NewHeap, NoLock);

	ereport(elevel,
			errmsg("repacking \"%s\" concurrently (Phase 2: swapping relation files)",
				   get_rel_name(tableOid)));

	pgstat_progress_update_param(PROGRESS_REPACK_PHASE,
								 PROGRESS_REPACK_PHASE_SWAP_REL_FILES);

	/*
	 * Swap the physical files of the old and new heaps, rebuild indexes,
	 * and drop the transient new heap.
	 */
	finish_heap_swap(tableOid, OIDNewHeap, is_system_catalog,
					 swap_toast_by_content, false, true,
					 frozenXid, cutoffMulti,
					 relpersistence);

	PopActiveSnapshot();
	CommitTransactionCommand();

	/*
	 * Release the session-level lock outside of any transaction, following
	 * the same pattern as REINDEX CONCURRENTLY.
	 */
	UnlockRelationIdForSession(&heaplockid, ShareUpdateExclusiveLock);

	/*
	 * Start a new transaction so the outer command loop can complete it.
	 * This matches the pattern used by REINDEX CONCURRENTLY.
	 */
	StartTransactionCommand();

	pgstat_progress_end_command();

	MemoryContextDelete(private_context);
}
