From FSPL Require Export Imp.

(* First we define syntax of the language *)

(* We could reuse aexp and bexp defined for Imp. *)

(* Redefine commands here. To distinguish them 
   from Imp commands, we call them scom *)
(* You need to change it into an inductive definition *)
Inductive scom : Type := 
  | SSkip : scom
  | SAss : id -> aexp -> scom
  | SSeq : scom -> scom -> scom
  | SIf : bexp -> scom -> scom -> scom
  | SWhile : bexp -> scom -> scom
  | SLoad : id -> aexp -> scom        (* x:=[e] *)
  | SStore: scom -> scom -> scom      (* [e]:=e' *)
  | SCons:  id -> aexp -> aexp -> scom(* x:=cons(e,e') *)
  | SDis : aexp -> scom .              (* dispose(e) *)

Notation "'SKIP'" :=
  SSkip.
Notation "x '::=' a" :=
  (SAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (SSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (SWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (SIf c1 c2 c3) (at level 80, right associativity).
Notation " x '::=' [ e ] " :=
  (SLoad x e) (at level 60).
Notation "[ e ] '::=' e' " :=
  (SStore e e') (at level 60).

(* Program states, which is called sstate *)
Definition store := id -> nat.

(* if heap maps a natural number (address) to
   None, we say the address is not a valid address,
   or it is not in the domain of the heap *)
Definition heap := nat -> option nat.

Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
    (forall (x: X), f x = g x) ->  f = g.

(* Define an empty heap, which contains no memory cells *)
Definition emp_heap : heap := 
  fun (l: nat) => None.

Definition in_dom (l: nat) (h: heap) : Prop :=
  exists n, h l = Some n.

Definition not_in_dom (l: nat) (h: heap) : Prop :=
  h l = None.

Theorem in_not_in_dec : 
  forall l h, {in_dom l h} + {not_in_dom l h}.
Proof.
  intros l h. unfold in_dom. unfold not_in_dom.
  destruct (h l).
  left. exists n. auto.
  right. auto.
Defined.

(* h1 and h2 have disjoint domain *)
Definition disjoint (h1 h2: heap) : Prop := 
  forall l, not_in_dom l h1 \/ not_in_dom l h2.

(* union of two heaps *)
Definition h_union (h1 h2: heap) : heap :=
  fun l => 
    if (in_not_in_dec l h1) then h1 l else h2 l.

(* h1 is a subset of h2 *)
Definition h_subset (h1 h2: heap) : Prop := 
  forall l n, h1 l = Some n -> h2 l = Some n.

(* store update *)
Definition st_update (s: store) (x: id) (n: nat) : store :=
  fun x' => if eq_id_dec x x' then n else s x'.

(* heap update *)
Definition h_update (h: heap) (l: nat) (n: nat) : heap :=
  fun l' => if eq_nat_dec l l' then Some n else h l'.

Definition sstate := (store * heap) %type.

(* since program may abort, we extend our state
   definition to add a special state Abt *)
Inductive ext_state : Type :=
  St:  sstate -> ext_state    (* normal state *)
| Abt: ext_state.             (* abort *)


(* Next we define the operational semantics *)

(* big-step semantics. You should change it into 
   an inductive definition *)
Reserved Notation "c '@' st '~>' st'" (at level 40, st at level 39).
Inductive big_step: 
   scom * sstate -> ext_state -> Prop := 
  | E_SSkip : forall st,
      SKIP @ st ~> St st
  | E_SAss : forall st id aexp n,
      aeval (fst st) aexp = n ->
      (id ::= aexp) @ st ~> (St ((update (fst st) id n), (snd st)))
  | E_SSeq : forall st st1 st2 c1 c2,
      c1 @ st ~> (St st1) ->
      c2 @ st1 ~> (St st2) ->
      (c1 ;; c2) @ st~> (St st2)
  | E_SIfTrue : forall st st1 b c1 c2,
      beval (fst st) b = true ->
      c1 @ st ~> (St st1) ->
      (IFB b THEN c1 ELSE c2 FI) @ st ~> (St st1)
  | E_SIfFalse : forall st st1 b c1 c2,
      beval (fst st) b = false ->
      c2 @ st ~> (St st1) ->
      (IFB b THEN c1 ELSE c2 FI) @ st ~> (St st1)
  | E_SWhileEnd: forall st b c,
      beval (fst st) b = false ->
      (WHILE b DO c END) @ st ~> (St st)
  | E_SWhileLoop: forall st st1 st2 b c,
      beval (fst st) b = true ->
      c @ st ~> (St st1) ->
      (WHILE b DO c END) @ st1 ~> (St st2) ->
      (WHILE b DO c END) @ st ~>  (St st2) 
  |E_STORE_T: forall aexp1 aexp2 st ,
      in_dom  (aeval (fst st) aexp1 ) (snd st) ->
      ([aexp1] ::= aexp2) # st ~> 
      St((fst st), h_update (snd st) (aeval (fst st) aexp1) (aeval (fst st) aexp2))
  where "c '@' st '~>' st' " := (big_step (c, st) st').

  (*Inductive scom : Type := 
  | SSkip : scom
  | SAss : id -> aexp -> scom
  | SSeq : scom -> scom -> scom
  | SIf : bexp -> scom -> scom -> scom
  | SWhile : bexp -> scom -> scom
  | SLoad : id -> aexp -> scom        (* x:=[e] *)
  | SStore: scom -> scom -> scom      (* [e]:=e' *)
  | SCons:  id -> aexp -> aexp -> scom(* x:=cons(e,e') *)
  | SDis : aexp -> scom .              (* dispose(e) *)
*)

(* small-step semantics. Should be inductive too *)
Definition small_step: 
   scom * ext_state -> scom * ext_state -> Prop 
  := admit.


(** Assertions **)
Definition sass := sstate -> Prop.

(* define semantics of assertion emp *)
Definition emp : sass := 
    fun st: sstate => 
      snd st = emp_heap.

(* assertion e1 |-> e2 *)
Definition pto (e1 e2: aexp) : sass := 
    fun st: sstate =>
      match st with
      | (s, h) => h = h_update emp_heap (aeval s e1) (aeval s e2)
      end.
Notation "e1 '|->' e2" := (pto e1 e2) (at level 60).

(* p * q *)
Definition star (p q : sass) : sass := 
    fun st: sstate =>
      match st with
      | (s, h) => 
        exists h1, exists h2, 
          disjoint h1 h2 /\ h_union h1 h2 = h /\ p (s, h1) /\ q (s, h2)
      end.
Notation "p '**' q" := (star p q) (at level 70).

(* p --* q *)
Definition simp (p q: sass) : sass := 
  fun (st : sstate) =>
    match st with
    | (s, h) => 
      forall h', disjoint h' h -> p (s, h') -> q (s, h_union h h')
    end.
Notation "p '--*' q" := (simp p q) (at level 80).


Definition pure (p: sass) : Prop := 
  forall s h1 h2, p (s, h1) -> p (s, h2).

Definition precise (p: sass) : Prop := 
  forall h h1 h2 s, 
     h_subset h1 h 
     -> h_subset h2 h 
     -> p (s, h1) 
     -> p (s, h2)
     -> h1 = h2.

Definition intuitionistic (p: sass) : Prop := 
  forall s h h', p (s, h) -> disjoint h h' -> p (s, h_union h h').


(* continue here *)

Definition s_conj (p q: sass) : sass :=
  fun (s: sstate) => p s /\ q s.
Notation "p '//\\' q" := (s_conj p q) (at level 75).

Definition s_disj (p q: sass) : sass :=
  fun (s: sstate) => p s \/ q s.
Notation "p '\\//' q" := (s_disj p q) (at level 78).

Definition s_imp (p q: sass) : sass :=
  fun (s: sstate) => p s -> q s.
Notation "p '~~>' q" := (s_imp p q) (at level 85).

Definition strongerThan (p q: sass) : Prop :=
  forall s: sstate, s_imp p q s.
Notation "p '==>' q" := (strongerThan p q) (at level 90).

Definition spEquiv (p q: sass) : Prop :=
  (p ==> q) /\ (q ==> p).
Notation "p '<==>' q" := (spEquiv p q) (at level 90).

(* Prove the following lemmas *)
Lemma disj_star_distr: forall (p q r: sass),
  (p \\// q) ** r <==> (p ** r) \\// (q ** r).
Admitted.  

Lemma conj_star_distr: forall (p q r: sass),
  (p //\\ q) ** r ==> (p ** r) //\\ (q ** r).
Admitted.

Lemma precise_conj_distr: forall (p q r: sass),
  precise r -> (p ** r) //\\ (q ** r) ==> (p //\\ q) ** r.
Admitted.
 
Inductive multiStep : 
    scom * ext_state -> scom * ext_state -> Prop :=
| step0: forall c s, multiStep (c, s) (c, s)
| stepn: forall c s c' s' c'' s'', 
           small_step (c, s) (c', s')
           -> multiStep (c', s') (c'', s'')
           -> multiStep (c, s) (c'', s'').

(* c is safe at state s *)
Definition safeAt (c: scom) (s: sstate) : Prop :=
(* ~ multiStep (c, St s) Abt *) 
(*
forall c' s',
  multiStep (c, St s) (c', St s')
  -> c' = SKIP \/ exists c'', exists s'', small_step (c', St s') (c'', St s'').
*)
admit.

Definition safeMono (c: scom) : Prop := 
(*
  forall s h h', 
    safeAt c (s, h) -> disjoint h h' -> safeAt c (s, h_union h h').
*)
admit.

Definition frame (c: scom) : Prop :=
  forall s h1 h2 c' s' h',
    safeAt c (s, h1) 
    -> disjoint h1 h2 
    -> small_step (c, St (s, h_union h1 h2)) (c', St (s', h'))
    -> exists h1', 
         small_step (c, St (s, h1)) (c', St (s', h1'))
         /\ disjoint h1' h2 
         /\ h_union h1' h2 = h'.

Theorem locality: forall c : scom, safeMono c /\ frame c.
Admitted.

