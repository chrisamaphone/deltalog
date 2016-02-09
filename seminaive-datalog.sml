(* Seminaive Implementation of Saturation for Propositional
 * Datalog
 * 7/31/12 Chris Martens
 * 
 * To get to seminaive from the naive algorithm:
 * 1. Index the rules by atoms appearing in their antecedent
 * 2. Maintain a queue of new facts that determine which
 *    rules are candidates to fire next (via the index)
 * 3. Fire all unconditional rules first and remove them
 *    from the rule base
 * 
 *)

functor PropSemiNaive
  (structure IS : INT_SET
   structure IM : INT_MAP) =
struct

  type atom = int
  datatype Neg =
	   Lolli of Pos * Neg
	 | Monad of Pos
       and Pos =
	   One
	 | Tensor of Pos * Pos
         | AtomPers of atom

  (* lookup : (Neg list) IM.map * atom -> Neg list
   * lookup (index, p) = rs, where rs are rules mentioning
   * p in the antecedent
   *)
  fun lookup (index, p) =
      (case IM.find (index, p)
	of NONE => nil
	 | SOME(rs) => rs)

  (* existsAll : Pos -> DB -> bool
   * existsAll S db = true if all atoms in S are in db
   *)
  fun existsAll (One) db = true
    | existsAll (Tensor(S1,S2)) db = existsAll S1 db andalso existsAll S2 db
    | existsAll (AtomPers(p)) db = IS.member (db, p)

  (* filterNew : Pos -> DB -> atom list -> atom list
   * filterNew S db newP = newP + newP', where newP'
   * are the atoms in S not already in db
   *)
  fun filterNew (One) db newP = newP
    | filterNew (Tensor(S1, S2)) db newP =
        filterNew S2 db (filterNew S1 db newP)
    | filterNew (AtomPers(p)) db newP =
      if IS.member (db, p) orelse List.exists (fn p' => p = p') newP
      then newP
      else p :: newP

  (* match : Neg -> DB -> atom list -> atom list
   * match A db ps = ps + ps', where ps'
   * are the new atoms in the succedent of A
   * (if A can fire) that are not already in db
   *)
  fun match (Monad(S)) db ps =
      filterNew S db ps
    | match (Lolli(S, A)) db ps =
      if existsAll S db
      then match A db ps
      else ps

  (* matchAll : Neg list -> DB -> atom list -> atom list
   * matchAll rs db ps = ps + ps' where ps'
   * are the new atoms in the succedents of all rules
   * is rs that can fire that are not already in db
   *)
  fun matchAll nil db ps = ps
    | matchAll (A::rs) db ps =
        matchAll rs db (match A db ps)

  (* fwdChain : Queue.queue -> DB -> (Neg list) IM.map -> DB
   * fwdChain q db index = db + db'
   * where db + db' is the saturation of db with rules
   * in index, based on atoms in q
   *)
  fun fwdChain q db index =
        fwdChain' (Queue.deq q) db index

   (* fwdChain' see fwdChain *)
  and fwdChain' NONE db index = db
    | fwdChain' (SOME(p, q)) db index =
      if IS.member(db, p)
      then fwdChain q db index
      else let
              val db' = IS.add(db, p)
              val candidates = lookup (index, p)
	      val ps = matchAll candidates db' nil
	      val q' = Queue.enqAll (q, ps)
	  in 
	      fwdChain q' db' index
	  end 

  (* indexPos : Pos -> Neg -> (Neg list) IM.map -> (Neg list) IM.map
   * indexPos S r index = index + index'
   * where index' maps atoms in S to r
   *)
  fun indexPos (One) r index = index
    | indexPos (Tensor(S1, S2)) r index =
      indexPos S2 r (indexPos S1 r index)
    | indexPos (AtomPers(p)) r index =
      IM.insert (index, p, r::lookup(index, p))

  (* indexRule : Neg -> Neg -> (Neg list) IM.map -> (Neg list) IM.map
   * indexRule A r index = index + index'
   * where index' maps atoms in the antecedents of A to r
   *)
  fun indexRule (Monad(S)) r index = index
    | indexRule (Lolli(S, A)) r index =
      indexRule A r (indexPos S r index)

  (* indexRules : Neg list -> (Neg list) IM.map -> (Neg list) IM.map
   * indexRules rs index = index + index'
   * where index' maps atoms to all rules in rs in whose antecedent
   * they appear
   *)
  fun indexRules nil index = index
    | indexRules (A::rs) index =
      indexRules rs (indexRule A A index)

  (* fwdChain0 : Neg list -> Queue.queue -> DB -> Neg list -> DB
   * fwdChain0 rs q db rbase = db + db'
   * where db' is the saturated version of db, after indexing the
   * rule base and preloading the queue with the succedent of
   * all unconditional rules
   *)
  fun fwdChain0 nil q db rbase = fwdChain q db (indexRules rbase IM.empty)
    | fwdChain0 (A::rs) q db rbase =
      (case match A db nil
	of nil => fwdChain0 rs q db (A::rbase)
         | ps => fwdChain0 rs (Queue.enqAll(q, ps)) db rbase)

  (* linChain n rbase = rs @ rbase
   * where rs are rules AtomPers(k-1) -o {AtomPers(k)} for 0 <= k <= n
   * and {AtomPers(0)}
   *)
  fun linChain 0 rbase = Monad(AtomPers(0))::rbase
    | linChain n rbase = linChain (n-1) (Lolli(AtomPers(n-1), Monad(AtomPers(n)))::rbase)

  (* test n
   * builds a program AtomPers(k-1) -o {AtomPers(k)} and
   * AtomPers(0) for 0 <= k <= n, saturates it, and test
   * the number of facts in the result
   *)
  fun test n =
      let val rbase0 = linChain n nil
	  val saturated = fwdChain0 rbase0 Queue.empty IS.empty nil
	  val len = IS.foldl (fn (p, n) => n+1) 0 saturated
      in 
	  len = n+1
      end

end

structure PropSemiNaiveSet =
  PropSemiNaive (structure IS = IntSet
                 structure IM = IntMap)
(*structure PropSemiNaiveList =
  PropSemiNaive (structure IS = IntList
                 structure IM = IntMap)*)
