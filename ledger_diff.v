Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Bool.Bool.

(* proof irrelevance axiom *)
Axiom proof_irrelevance : forall p : Prop, forall pf pf' : p, pf = pf'.

(* Maybe *)
Inductive maybe `(A : Type) :=
  | Just : A -> maybe A
  | Nothing : maybe A.

(* State update procedure *)
Variable updateState : forall (Tx : Type) (State : Type), Tx -> maybe State -> maybe State.

(* State update procedure *)
Variable initState : forall (Tx : Type) (State : Type), State.

Definition Ledger (Tx : Type) : Type := list Tx.

Fixpoint stateFoldL (Tx : Type) (State : Type) (l : Ledger _) (s : maybe State) : maybe State := 
  match l with
  | nil => s
  | h :: tl => updateState Tx State h (stateFoldL _ _ tl s)
  end.

Definition state (Tx : Type) (State : Type) (l : Ledger Tx) : maybe State := 
  stateFoldL _ _ l (Just _ (initState Tx State)).

Definition validLedger (Tx : Type) (State : Type) l := ~ state Tx State l = Nothing _.

Definition validLedgerState (Tx : Type) (State : Type) s := exists l, state Tx State l = Just _ s.

(* validation of a transaction *)
(* state update cannot be completed if the transaction is invalid in the starting state *)
Definition validateTx (Tx : Type) (State : Type) : 
  Tx -> maybe { s : State | validLedgerState Tx State s } -> bool :=
fun tx s =>
  match s with 
  | Just _ js => match (updateState _ _ tx (Just _ (proj1_sig js))) with
    | Just _ js => true
    | Nothing _ => false
    end
  | Nothing _ => true
  end.

(* Tim's Diff definition *)
Class Diff (A : Type) (diff : Type) :=
  {
    applyDiff : A -> diff -> A ;
    extend : diff -> diff -> diff ;
    zero : diff ;

    zeroChanges : forall x, applyDiff x zero = x ;

    applyExtend : forall x dx1 dx2, 
      applyDiff x (extend dx2 dx1) = applyDiff (applyDiff x dx1) dx2 ;

  }.

Definition inSub  (Tx : Type) (State : Type) (s : State) : 
  validLedgerState Tx State s -> {s : State | validLedgerState Tx State s}.
intro p. exists s. exact p.
Defined.

(* either applying a transaction to a valid state gives a new valid state, or it
returns Nothing *)
Definition nextValid (Tx : Type) (State : Type) (tx : Tx) (s : State) : forall vls : validLedgerState Tx State s,
  match (updateState _ _ tx (Just State s)) with 
  | Just _ js => (validLedgerState Tx State js)
  | Nothing _ => True end.
Proof.
  intro p. unfold validLedgerState in p. destruct p. rewrite <- H.
  unfold validLedgerState. 
  destruct (updateState _ _ tx (state _ _ x)) eqn:H1; auto.
  exists (tx :: x). rewrite <- H1. compute. auto. 
Qed.

(* apply a list of transaction to a valid state *)
Definition apdvl (Tx : Type) (State : Type) : maybe { s : State | validLedgerState Tx State s } -> (list Tx) 
  -> maybe { s : State | validLedgerState Tx State s }.
intros spm lstx. destruct spm as [js | ].
Focus 2. exact (Nothing _).
destruct js as [s p]. 
induction lstx. 
exact (Just _ (inSub _ _ s p)).
generalize (nextValid _ _ a s p). intro.
destruct (updateState _ _ a (Just State s)) eqn:H3.
exact (Just _ (inSub _ _ s0 H)).
exact (Nothing _).
Defined. 

(* valid ledger statess are the same even with different proof of validity *)
Definition pf_ir_state (Tx: Type) (State : Type) (s s' : maybe { s : State | validLedgerState Tx State s } ) :
(match s with
| Just _ js => match s' with 
  | Just _ js' => proj1_sig js = proj1_sig js' 
  | Nothing _ => False end
| Nothing _ => match s' with 
  | Just _ js => False 
  | Nothing _ => True end end) -> s = s'.
Proof. 
  intro. destruct s; destruct s'; compute; auto. 
  destruct s; destruct s0. compute in H. compute.
  generalize v. generalize v0. clear v. clear v0. rewrite H.
  intros. generalize (proof_irrelevance _ v v0). intro. rewrite H0.
  auto. tauto. tauto.
Qed.

(* need to finish this proof of 2nd equality in Diff class *)
Proposition applyExtendLS (Tx : Type) (State : Type) : forall x dx1 dx2, 
      apdvl Tx State x (dx1 ++ dx2) = apdvl _ _ (apdvl _ _ x dx1) dx2.
Proof.
  intros s ls1 ls2. destruct s as [js | ]. 
  destruct js as [s p]. 
  induction ls1; intros; auto. 
  assert ((a :: ls1) ++ ls2 = a :: (ls1 ++ ls2)).
  compute. auto. rewrite H.  
Admitted.

(* instance of Diff class for (maybe) valid ledger states and maps between them 
expressed as lists of transactions to be applied *)
Instance diffLS (Tx : Type) (State : Type) : Diff (maybe { s : State | validLedgerState Tx State s }) (list Tx).
exists
  (* applyDiff *)
    ( apdvl _ _ )
  (* extend *)
    ( fun ls2 ls1 => ls1 ++ ls2 )
  (* zero *)
    ( nil ).
Proof. 
(* zeroChanges *)
  intros s. destruct s as [js | ]. 
  destruct js as [s p]. 
  compute. auto.
  compute; auto.
(* applyExtend *)
  generalize applyExtendLS. auto.
Defined.

(* F represents the type of maps A -> B which are differentiable *)
(* maybe version of differentiation *)
Class Differentiable (A B F : Type) (apply : F -> maybe A -> maybe B) := 
  {
    (* diff's of A and B *)
    DiffTypeA : Type ;
    DiffClassA : Diff (maybe A) DiffTypeA ;
    DiffTypeB : Type ;
    DiffClassB : Diff (maybe B) DiffTypeB ;

    (* type of derivatives of F-type maps *)
    Fdiff : Type ;
    diffApp : Fdiff -> A -> DiffTypeA -> DiffTypeB ;

    (* differentiation operator *)
    fdiff : F -> Fdiff ;

    (* diff must satisfy this equality *)
    (* IF both 
        - applying the diff first, then applying f, AND
        - applying f, then applying the diff to the resulting state
        Are NOT Nothing, THEN 
        lhs = rhs *)
    diffRule : forall (f : F) (a : A) (da : DiffTypeA), 
        match (apply f (applyDiff (Just _ a) da)) with
        | Nothing _ => True
        | Just _ lhs => match applyDiff (apply f (Just _ a)) (diffApp (fdiff f) a da) with 
          | Nothing _ => True 
          | Just _ rhs => lhs = rhs
          end
        end

      (* without maybe case-matching this looks like :
      apply f (applyDiff a da) = applyDiff (apply f a) (diffApp (fdiff f) a da) ,
      or, without `apply`, like 
      f (applyDiff a da) = applyDiff (f a) (f' a da) *)
  }.

(* if two lists of transaction contain the same transactions (are permutations of each other),
and updating a state s with both lists succeed, both updates will result in the same state*)
Definition deterministicPerms (Tx : Type) (State : Type) := 
  forall s ls ls', 
  Permutation ls ls' -> 
          match (apdvl Tx State s ls) with
        | Nothing _ => True
        | Just _ lhs => match (apdvl Tx State s ls') with 
          | Nothing _ => True 
          | Just _ rhs => lhs = rhs
          end
        end.

Proposition moveOne (Tx : Type) : forall (ls ls' : Ledger Tx) (a : Tx), Permutation (a :: ls ++ ls') (ls ++ (a :: ls')).
Proof.
  intros. induction ls. compute. auto.
  replace ((a0 :: ls) ++ a :: ls') with (a0 :: (ls ++ a :: ls')).
  generalize (perm_swap a0 a (ls ++ ls')). intro ps. 
  generalize (@perm_trans Tx (a :: a0 :: ls ++ ls') (a0 :: a :: ls ++ ls') (a0 :: ls ++ a :: ls') ps).
  auto.
  compute. auto.
Qed.

Proposition listOrder (Tx : Type) : forall (ls ls' : Ledger Tx), Permutation (ls++ls') (ls'++ls).
Proof. 
  intros. induction ls. replace (ls' ++ nil) with ls'. compute. auto.
  induction ls'; compute; auto. compute in IHls'. rewrite <- IHls'. auto.
  generalize (perm_skip a IHls). intro pa.
  replace ((a :: ls) ++ ls') with (a :: ls ++ ls'). 
  generalize (moveOne _ ls' ls a). intro.
  generalize (@perm_trans Tx (a :: ls ++ ls') (a :: ls' ++ ls) (ls' ++ a :: ls) pa).
  auto. compute. auto.
Qed.

(* given that permuting transactions in a list applied to a state does not affect the 
resulting state --- if both permutations result in valid states, 
we can define a ledger that is an instance of the Differentiable class *)
Instance diffLedger (Tx : Type) (State : Type) (dp : deterministicPerms Tx State) : 
  Differentiable ({ s : State | validLedgerState Tx State s }) 
  ({ s : State | validLedgerState Tx State s })  (list Tx) (fun ltx ms => apdvl _ _ ms ltx).
exists
(* DiffTypeA *)
  (list Tx)
(* Diff Class A *)
  (diffLS Tx State)
(* DiffTypeB *)
  (list Tx)
(* Diff Class B *)
  (diffLS Tx State)
(* Fdiff *)
  (list Tx)
(* diffApp *)
  (fun f' a da => da)
(* fdiff *)
  (fun f => f).
Proof.
  intros. unfold deterministicPerms in dp.
  generalize (dp (Just _ a) (f++da) (da++f) (listOrder _ f da)). intros. 
  generalize (applyExtend (Just {s : State | validLedgerState _ _ s} a) da f).
  replace applyDiff with (apdvl Tx State). 
  intro. replace (extend f da) with (da ++ f) in H0.
  rewrite <- H0.
  generalize (applyExtend (Just {s : State | validLedgerState _ _ s} a) f da). intro.
  replace applyDiff with (apdvl Tx State) in H1. replace (extend da f) with (f ++ da) in H1.
  rewrite <- H1.
  destruct (apdvl _ _ (Just {s : State | validLedgerState _ _ s} a) (da ++ f)).
  destruct (apdvl _ _ (Just {s0 : State | validLedgerState _ _ s0} a) (f ++ da)).
  rewrite H. auto. auto. auto. simpl. auto. simpl. auto. simpl. auto. simpl. auto.
Defined.

(* This statement corresponds to the deterministic ledger definition given in 
terms of delta : (S -> S) -> DiffMap, proof is immediate *)
Proposition deterministicLedger (Tx : Type) (State : Type) (dp : deterministicPerms Tx State) :
  forall tx s s', 
  match (s, s', (validateTx Tx State tx s), (validateTx Tx State tx s')) with 
  | (Just _ js, Just _ js', true, true) => 
    forall da : DiffTypeA,
    diffApp (@fdiff _ _ _ _ (diffLedger Tx State dp) (tx::nil)) js da = diffApp (fdiff (tx::nil)) js' da
  | _ => True
  end.
Proof.
  intros. destruct s; auto. destruct s'; auto. 
  destruct (validateTx _ _ tx (Just {s1 : State | validLedgerState _ _ s1} s)); auto.
  destruct (validateTx _ _ tx (Just {s1 : State | validLedgerState _ _ s1} s0)); auto.
Qed.

(* diffRule type for ledgers *)
Definition diffRuleLedgers (Tx : Type) (State : Type) :=
  forall (f : list Tx) (a : {s : State | validLedgerState Tx State s})
    (da : list Tx),
  match
    apdvl Tx State
      (apdvl Tx State (Just {s : State | validLedgerState Tx State s} a) da) f
  with
  | Just _ lhs =>
      match
        apdvl Tx State
          (apdvl Tx State (Just {s : State | validLedgerState Tx State s} a) f) da
      with
      | Just _ rhs => lhs = rhs
      | Nothing _ => True
      end
  | Nothing _ => True
  end.

(* an instance of Differentiable for a ledger that assumes the proof obligations rather than deterministicPerms *)
Instance diffLedgerDR (Tx : Type) (State : Type) (dr : diffRuleLedgers Tx State) : 
  Differentiable ({ s : State | validLedgerState Tx State s }) 
  ({ s : State | validLedgerState Tx State s })  (list Tx) (fun ltx ms => apdvl _ _ ms ltx).
exists
(* DiffTypeA *)
  (list Tx)
(* Diff Class A *)
  (diffLS Tx State)
(* DiffTypeB *)
  (list Tx)
(* Diff Class B *)
  (diffLS Tx State)
(* Fdiff *)
  (list Tx)
(* diffApp *)
  (fun f' a da => da)
(* fdiff *)
  (fun f => f).
Proof.
(* diffRule *)
  exact dr.
Defined.

(* WANT : Given any ledger that is an instance of the Differentiable clas (with all the types 
the same as the diffLedger instance), deterministicPerms is True *)
Proposition dpAllDiffLedgers (Tx : Type) (State : Type) (dr : diffRuleLedgers Tx State) :  
  deterministicPerms Tx State.
unfold deterministicPerms. unfold diffRuleLedgers in dr.
intros. inversion H. 
destruct (apdvl Tx State s nil); auto.
generalize (dr 
ls. 
replace ls' with (@nil Tx).
symmetry.
apply Permutation_nil. auto.
induction ls'.
assert ((a :: ls) = nil).
apply Permutation_nil.
apply Permutation_sym. auto. inversion H0.

intro.
 int
destruct (apdvl Tx State s nil); auto.
induction ls. 
compute. auto.


(* NOTE :
If we try to define delta for any two states (if we consider them as points of State object in the 
category of ledgers), we fail, because the only maps we have to choose from 
are those corresponding to lists of transaction producing valid ledger updates. So,
Definition delta : Ledger -> Ledger -> DeltaType
- is the wrong type *)

(* instead we want the delta made by a FUNCTION f : Ledger -> Ledger, ie. some list ls : list Tx, applied 
Definition delta : (Ledger -> Ledger) -> DeltaType
- which is exactly the differentiation operator fdiff in the following instance of class Differentiable 
*) 

(* Objects in the category of ledgers *)
Definition LedgerOb (Tx : Type) 
  (State : Type) 
  (updateState : Tx -> maybe { s : State | validLedgerState Tx State s } 
    -> maybe { s : State | validLedgerState Tx State s })
  (initState : State) := (Tx, State, updateState, initState). 

Definition AnyHomLedgerOb 
(* source object *)
  (Tx : Type) 
  (State : Type) 
  (updateState : Tx -> maybe { s : State | validLedgerState Tx State s } -> maybe { s : State | validLedgerState Tx State s })
  (initState : State) 
(* Target Object *)
  (Tx' : Type) 
  (State' : Type) 
  (updateState' : Tx' -> maybe { s : State' | validLedgerState Tx' State' s } -> maybe { s : State' | validLedgerState Tx' State' s })
  (initState' : State') := (Tx -> Tx', maybe { s : State | validLedgerState Tx State s } -> maybe { s : State' | validLedgerState Tx' State' s }).

(* a morphism between two ledgers is a map between tranactions and states that preserves updates and initial state *)
(* need some way to specify that initial state is special and valid *)
(* this is wrong because need to parametrize validLedgerState by updateState *)
(* how do you make all these params implicit?? *)
Definition HomLedgerOb 
(* source object *)
  (Tx : Type) 
  (State : Type) 
  (updateStateMaybe : Tx -> maybe State -> maybe State)
  (initState : State) 
(* Target Object *)
  (Tx' : Type) 
  (State' : Type) 
  (updateStateMaybe' : Tx' -> maybe State' -> maybe State')
  (initState' : State') :=
  { ahl : AnyHomLedgerOb Tx State updateStateMaybe' initStateMaybe Tx' State' updateStateMaybe' initStateMaybe' |
  forall (tx : Tx) (s : State),
  updateState tx s = updateState' ((fst ahl) tx) ((snd ahl) s) /\
  (snd ahl) initState = initState' }.


(* Compositions and identity are also exactly what you would expect - given in Diff class *)

(* ANDRE's COMMENTS
Turns out morphisms are super easy. Just a pair of functions 
f_state : State_L -> State_L' and f_tx : Tx_L -> Tx_L' such that all the obvious equations for 
initState, updateState and validate are satisfied



Monomorphisms are those where both functions are injective

But the way you model threads doesn't match up with monomorphisms, I think it matches much more 
closely with epimorphisms of the form L -> (T + 1) where T is the ledger belonging to the thread T, 
with terminal object 1 and coproduct + (assuming those exist, which I haven't checked). Your 
condition (2) ensures that it's an epimorphism. (edited) 

Which I think suggests an alternative definitions of threads: epimorphisms \u03c0 : L -> T. If you then 
want a thread to have a halting state, you can actually specify it, but it doesn't have to have one. 
But since it's a morphism, you still have \u03c0 (initState_L) = initState_T, so the thread always starts at 
its initial state.

(this would mean that there's no real state of it on-chain though, since initState_L is the genesis 
state. So to have an initial state that also has some data in it, there'd have to be a transaction 
for T that actually initializes it)

Here's a problem though: the isomorphisms of the category are bad. The issue is validate: it doesn't 
have any relations with anything else, so any two ledgers that are the same except with two different 
validate functions are isomorphic, which is probably not good. I think this suggests that there should 
either be some law regarding validate, or it should be removed by making updateState partial instead

Other than that, I think the category seems pretty well behaved. I haven't fully checked everything, 
but I think it has at least all finite limits and colimits, with the only slightly weird one being the 
initial object (it has a single state and no transactions) and everything else are what you'd expect

One problem with modeling a thread as an epimorphism is that every transaction would also correspond 
to a transaction of the thread, so in practice every thread would need to have a doNothing transaction. 
Monomorphisms don't have that problem, but then you don't get the projection function for free, and every 
transaction in the thread would also automatically be equipped with a 'canonical' transaction in the 
ledger that executes this action. The projection function could of course be then an additional requirement
 for the thread, but I don't know if those canonical transactions are something one would want. 
A weaker version of that would be to not choose a monomorphism, but just have a thread be a ledger 
such that there exists a monomorphism.

Oh, I think I was wrong about colimits existing, I don't think the category has coproducts. The issue is 
that it's not clear what initial state to pick, and the two inclusion maps require different ones

Maybe coproducts still do exist, just not with the naive approach
*)
