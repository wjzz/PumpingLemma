(* In this file we try to formalize some notions from the 
   formal languages field, precisely 
   Deterministic Finite-State Automata.
 *)

Require Import List.
Load Repeats.
Section Transitions.

(*
 * 
 * The basic components of an automata 
 *
 *)

(* The type of states *)
Variable Q: Type.

(* The number of possible states *)
(* Or as the states_size axiom states, any upper bound on
   the number of possible states *)
Variable Q_size : nat.

(* The type of alfabet's symbols *)
Variable Sigma: Type.

(* The transition function *)
Parameter d: Q -> Sigma -> Q.

(* A function that decides if the given state is an accepting state *)
Parameter is_accepting: Q -> Prop.

(* The initial state *)
Variable q0 : Q.


Axiom states_size: forall l: list Q, length l > Q_size ->
  repeats l.


(* Extension of a transition function *)
Fixpoint ext (q: Q) (l: list Sigma) : Q :=
  match l with
  | nil => q
  | h :: t => ext (d q h) t
  end.

Theorem ext_app: forall xs ys: list Sigma, forall q: Q,
  ext q (xs ++ ys) = ext (ext q xs) ys.
Proof.
  induction xs ; simpl ; congruence.
Qed.

(* Defines when a word is accepted *)
Definition accepted_word (w: list Sigma) :=
  is_accepting (ext q0 w).


Ltac dfa_rew := autorewrite with dfa_trans ; try congruence ; auto.

Hint Rewrite ext_app : dfa_trans.
Hint Rewrite map_length : dfa_trans.


Fixpoint word_replicate (n: nat) (l: list Sigma) : list Sigma :=
  match n with
  | O => nil
  | S n' => l ++ word_replicate n' l
  end.

(* If there is a loop in the automata, then we can exploit it,
   by duplicating the word that is looping it *)
Theorem ext_loop: forall n:nat, forall q: Q, forall xs: list Sigma,
  ext q xs = q -> ext q (word_replicate n xs) = q.
Proof.
  induction n as [|n']; trivial.
  
  (* n = S n; *)
  intros q xs H.
  simpl. dfa_rew. rewrite H. 
  apply IHn'. assumption.
Qed.

Fixpoint inits {X: Type} (l: list X) :list (list X) :=
  match l with
  | nil => nil :: nil
  | x :: xs => nil :: map (cons x) (inits xs)
  end.

Eval compute in (inits (1::2::nil)).
Eval compute in (inits nil : list (list nat)).

Theorem inits_len: forall X: Type, forall l: list X,
  length (inits l) = S (length l).
Proof.
  induction l ; trivial.
  (* l = cons _ _ *)
  simpl ; dfa_rew .
Qed.

Hint Rewrite inits_len : dfa_trans.

Theorem inits_dec_1: 
  forall X: Type, 
  forall l:list X,
  forall y: list X, 
  forall xs ys: list (list X),
   inits l = xs ++ (y::ys) -> 
    exists zs: list X, l = y ++ zs.
Proof.
  intros X l. induction l as [|h l'].
  
  (* l is nil *)
  intros y xs ys H.
  
  (* y has to be nil *)
  simpl in H.

  assert (xs = nil) as Hxs.
  destruct xs ; auto. destruct xs ; auto ; simpl in * ; inversion H.
  subst xs. simpl in H. inversion H. exists nil. auto.

  (* l is h :: l' *)
  intros y xs ys H.
  simpl in H.
  destruct xs.
  simpl in H.
  inversion H. exists (h :: l'). auto.

  simpl in H ; inversion H.
  
  apply map_dec_2 in H2.
  destruct H2 as [xss].
  destruct H0 as [yss].
  destruct H0. destruct H2.
  destruct yss as [|y0 yss].
  inversion H3.
  simpl in H3.
  apply IHl' in H0.
  destruct H0 as [zs].
  inversion H3.
  simpl. exists zs.
  subst. auto.
Qed.


Theorem inits_dec_2: 
  forall X: Type, 
  forall l: list X,
  forall y z: list X, 
  forall xs ys zs: list (list X),
   inits l = xs ++ (y::ys) ++ (z::zs) -> 
    exists ds: list X, z = y ++ ds /\ length ds > 0.
Proof.
  intros X l. induction l as [|h l'].
  intros y z xs ys zs H.
  
  (* Impossible case, inits nil has 1 elem,
     the list on RHO has >= 2 elems *)
  destruct xs.
  simpl in H.
  inversion H.
  subst y. simpl in *.
  inversion H.
  destruct ys ; simpl in * ; inversion H1.
  simpl in *. inversion H.
  subst l. inversion H.
  destruct xs.
  simpl in *. inversion H2.
  simpl in *; inversion H1.
  
  (* l = h :: l' *)
  
  (* we need more info *)
  destruct l' as [|h' ls].
  intros y z xs ys zs H.
  simpl in *.
  destruct xs.
  simpl in *.
  inversion H.
  subst y.
  inversion H.
  destruct ys.
  simpl in *.
  inversion H1.
  exists (h :: nil).
  split ; auto.
  inversion H1.
  simpl in *. clear H2. clear H.
  destruct ys ; simpl in * ; inversion H4.
  inversion H.
  destruct xs.
  simpl in *.
  inversion H2.
  destruct ys ; simpl in * ; inversion H4.
  inversion H2.
  destruct xs ; simpl in H4 ; inversion H4.

  (* l = h :: h' :: ls *)

  (* finally we can use the ind. hyp. *)
  
  intros y z xs ys zs H.
  remember (h' :: ls) as l.
  simpl in *.
  destruct xs.
  simpl in *; inversion H.

  exists z. split; auto.
  apply map_dec_2 in H2.
  destruct H2 as [xss].
  destruct H0 as [yss].
  destruct H0. destruct H2.
  destruct yss ; simpl in * ; inversion H3.
  simpl ; auto with arith.

  simpl in *.
  inversion H.
  subst l0. clear H.

  assert (map (cons h) (inits l) = xs ++ (y::ys) ++ (z::zs)).
  simpl ; auto.
  apply map_dec_3 in H.
  destruct H as [xss].
  destruct H as [yss].
  destruct H as [zss].
  destruct H. destruct H0. destruct H1.
  destruct yss ; simpl in * ; inversion H1.
  destruct zss ; simpl in * ; inversion H3.

  apply IHl' in H.
  destruct H as [ds].
  destruct H.
  exists ds. split ; subst ; auto.
Qed.

Theorem inits_dec: forall X: Type, forall l: list X,
  forall b c: list X, forall ass bs cs: list (list X),
  inits l = ass ++ (b::bs) ++ (c::cs) -> 
  (exists ds: list X, c = b ++ ds /\ 
    length ds > 0) /\ 
  exists es: list X, l = c ++ es.
Proof.
  intros X l b c ass bs cs H.
  remember H as H2 ; clear HeqH2.
  apply inits_dec_2 in H.
  destruct H as [ds].
  split.
  exists ds.
  destruct H.
  split ; try split ; auto.
  rewrite app_assoc in H2.
  eapply inits_dec_1. eauto.
Qed. 


Definition prefixes (q: Q) (l: list Sigma) : list Q :=
  map (ext q) (inits l).

Lemma prefixes_len: forall l: list Sigma, forall q: Q,
  length (prefixes q l) = S (length l).
Proof.
  intros ; unfold prefixes ; dfa_rew.
Qed.

(* Now we can state the pumping lemma: *)
Theorem pumping_lemma: forall w: list Sigma,
  accepted_word w -> Q_size <= length w -> 
  exists xs : list Sigma,
  exists ys : list Sigma,
  exists zs : list Sigma, 
  length ys > 0 /\
 (* length ys < Q_size -> *)
  w = xs ++ ys ++ zs /\
  forall n:nat, 
  accepted_word (xs ++ (word_replicate n ys) ++ zs).
Proof.
  intros w acc len_w.
  (* Let's look at which state the DFA is after reading
  epsilon, w0, w0w1, .. w. *)
  set (pref := prefixes q0 w).

  assert (Hpref: Q_size < length pref).
  unfold pref. rewrite prefixes_len. auto with arith.

  assert (HRep: repeats pref).
  apply states_size. auto.

  set (Hx := repeats_decomp Q pref HRep).
  destruct Hx. destruct H. destruct H. destruct H. 
  unfold pref in H. unfold prefixes in H.
  
  set (Hx := map_dec_3 (list Sigma) Q (ext q0)
      (inits w) x0 (x::x1) (x::x2) H).
  destruct Hx. destruct H0. destruct H0. destruct H0.
  destruct H1. destruct H2.

  (* x4 and x5 can;t be nil *)
  destruct x4 as [|y x4]. inversion H2.
  destruct x5 as [|y2 x5]. inversion H3.
  
  set (Hx := inits_dec _ w y y2 x3 x4 x5 H0).
  destruct Hx. destruct H4. destruct H5.
  destruct  H4.
  exists y. exists x6. exists x7.
  split ; try split.
  auto.

  subst y2. rewrite H5. rewrite app_assoc. auto.

  
  unfold accepted_word in *.
  intros n.
  assert (ext q0 (y ++ (word_replicate n x6) ++ x7) = ext q0 w).
  dfa_rew.
  simpl in H2.
  inversion H2.
  simpl in H3.
  inversion H3.

  
  assert (ext (ext q0 y) x6 = ext q0 y).
  pattern (ext q0 y) at 2. rewrite H8.
  rewrite <- H10.
  rewrite H4.
  dfa_rew.
  
  rewrite ext_loop ; auto.
  rewrite H5. dfa_rew.

  rewrite H7. auto.
Qed.
