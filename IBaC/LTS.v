Require Import String List.
Import ListNotations.

Inductive Action : Type := action : string -> Action.

CoInductive Process : Type :=
| process : list (Action * Process) -> Process.

Inductive mu_derivative : Action -> Process -> Process -> Prop :=
| derivative_here : forall a q l, mu_derivative a (process ((a, q) :: l)) q
| derivative_later : forall a a' l q q', mu_derivative a (process l) q ->
                                   mu_derivative a (process ((a', q') :: l)) q.

CoInductive Bisimilar : Process -> Process -> Prop :=
| bisimilar : forall p q,
                   (forall p' mu, mu_derivative mu p p' -> exists q', mu_derivative mu q q' /\ Bisimilar p' q') ->
                   (forall q' mu, mu_derivative mu q q' -> exists p', mu_derivative mu p p' /\ Bisimilar p' q') ->
                   Bisimilar p q.

Definition destruct (p : Process) : Process :=
  match p with
    | process l => process l
  end.

Lemma destruct_eq : forall p, p = destruct p.
Proof.
  destruct p; auto.
Qed.

Module Ex1.
  CoFixpoint p1 := process [(action "a", p2)]
  with p2 := process [(action "b", p1)].

  CoFixpoint q1 := process [(action "a", q2)]
  with q2 := process [(action "b", q3)]
  with q3 := process [(action "a", q2)].

  Goal Bisimilar p1 q1.
  Proof.
    cofix.
    rewrite (destruct_eq p1).
    rewrite (destruct_eq q1).
    simpl.
    assert (Bisimilar p2 q2).
      cofix.
      rewrite (destruct_eq p2).
      rewrite (destruct_eq q2).
      simpl.
      assert (Bisimilar p1 q3).
        cofix.
        rewrite (destruct_eq p1).
        rewrite (destruct_eq q3).
        simpl.
        constructor; intros.
          inversion H; subst.
            exists q2.
            split; auto; constructor.

            inversion H5.
          inversion H; subst.
            exists p2.
            split; auto; constructor.

            inversion H5.
      constructor; intros.
        inversion H0; subst.
          exists q3.
          split; auto; constructor.

          inversion H6.
        inversion H0; subst.
          exists p1.
          split; auto; constructor.

          inversion H6.
    constructor; intros.
      inversion H0; subst.
        exists q2.
        split; auto; constructor.

        inversion H6.
      inversion H0; subst.
        exists p2.
        split; auto; constructor.

        inversion H6.
  Qed.
End Ex1.

Module Ex2.
  CoFixpoint p1 := process [(action "a", p2); (action "a", p3)]
  with p2 := process [(action "b", p1)]
  with p3 := process [(action "c", p1)].

  Goal Bisimilar p1 p1.
  Proof.
    cofix.
    rewrite (destruct_eq p1).
    simpl.
    assert (Bisimilar p2 p2).
      cofix.
      rewrite (destruct_eq p2).
      simpl.
      constructor; intros.
        inversion H; subst.
          exists p1.
          split; auto; constructor.
          inversion H5.
        inversion H; subst.
          exists p1.
          split; auto; constructor.
          inversion H5.
    assert (Bisimilar p3 p3).
      cofix.
      rewrite (destruct_eq p3).
      simpl.
      constructor; intros.
        inversion H0; subst.
          exists p1.
          split; auto; constructor.
          inversion H6.
        inversion H0; subst.
          exists p1.
          split; auto; constructor.
          inversion H6.
    constructor; intros.
      inversion H1; subst.
        exists p2.
        split; auto; constructor.
        inversion H7; subst.
          exists p3.
          split; auto; constructor.
          inversion H8.
      inversion H1; subst.
        exists p2.
        split; auto; constructor.
        inversion H7; subst.
          exists p3.
          split; auto; constructor.
          inversion H8.
  Qed.
End Ex2.

Theorem refl : forall p, Bisimilar p p.
Proof.
  cofix.
  constructor; intros.
    exists p'.
    split; auto.
    exists q'.
    split; auto.
Qed.

Theorem symm : forall p q, Bisimilar p q -> Bisimilar q p.
Proof.
  cofix.
  constructor; intros.
    inversion H; subst.
    apply H2 in H0.
    inversion H0.
    inversion H3.
    exists x.
    split; auto.

    inversion H; subst.
    apply H1 in H0.
    inversion H0.
    inversion H3.
    exists x.
    split; auto.
Qed.

Theorem trans : forall p q r, Bisimilar p q -> Bisimilar q r -> Bisimilar p r.
Proof.
  cofix.
  constructor; intros.
    inversion_clear H; subst.
    apply H2 in H1.
    inversion_clear H1.
    inversion_clear H.
    inversion_clear H0; subst.
    apply H in H1.
    inversion_clear H1.
    inversion_clear H0.
    exists x0.
    split; auto.
    apply trans with x; auto.

    inversion_clear H; subst.
    inversion_clear H0; subst.
    apply H4 in H1.
    inversion_clear H1.
    inversion_clear H0.
    apply H3 in H1.
    inversion_clear H1.
    inversion_clear H0.
    exists x0.
    split; auto.
    apply trans with x; auto.
Qed.

CoInductive WrongBisimilar : Process -> Process -> Prop :=
| wrong_bisimilar : forall p q,
                   (forall p' mu, mu_derivative mu p p' -> forall q', mu_derivative mu q q' -> WrongBisimilar p' q') ->
                   (forall q' mu, mu_derivative mu q q' -> forall p', mu_derivative mu p p' -> WrongBisimilar p' q') ->
                   WrongBisimilar p q.

Goal forall p q, WrongBisimilar p q.
Proof.
  cofix.
  constructor; auto.
Qed.

Module Ex3.
  CoFixpoint p1 := process [(action "a", p2); (action "a", p3)]
  with p2 := process []
  with p3 := process [(action "b", p4)]
  with p4 := process [].

  CoFixpoint q1 := process [(action "a", q2)]
  with q2 := process [(action "b", q3)]
  with q3 := process [].

  Goal ~ Bisimilar p1 q1.
  Proof.
    rewrite (destruct_eq p1).
    rewrite (destruct_eq q1).
    simpl.
    intro.
    inversion H; subst.
    assert (mu_derivative (action "a") (process [(action "a", p2); (action "a", p3)]) p2).
      constructor.
    apply H0 in H2.
    inversion_clear H2.
    inversion_clear H3.
    inversion H2; subst.
      rewrite (destruct_eq p2) in H4.
      rewrite (destruct_eq q2) in H4.
      simpl in H4.
      inversion H4; subst.
      assert (mu_derivative (action "b") (process [(action "b", q3)]) q3).
        constructor.
      apply H5 in H6.
      inversion_clear H6.
      inversion_clear H7.
      inversion H6.
    inversion H9.
Qed.

Inductive multi_step_derivative : list Action -> Process -> Process -> Prop :=
  | multi_derivative_here : forall a p q, mu_derivative a p q -> multi_step_derivative [a] p q
  | multi_derivative_later : forall a l p q r, mu_derivative a p q ->
                                               multi_step_derivative l q r ->
                                               multi_step_derivative (a :: l) p r.

CoInductive Multi_bisimilar : Process -> Process -> Prop :=
| bulti_bisimular : forall p q,
                      (forall p' mu, multi_step_derivative mu p p' ->
                                     exists q', multi_step_derivative mu q q' /\ Multi_bisimilar p' q') ->
                      (forall q' mu, multi_step_derivative mu q q' ->
                                     exists p', multi_step_derivative mu p p' /\ Multi_bisimilar p' q') ->
                      Multi_bisimilar p q.

Goal forall p q, Bisimilar p q <-> Multi_bisimilar p q.
Proof.
  split; generalize dependent p; generalize dependent q; cofix.
    intros.
    constructor; intros.
      induction H0; subst.
        inversion H; subst.
        apply H1 in H0.
        inversion_clear H0.
        inversion_clear H3.
        exists x.
        split.
          apply multi_derivative_here; auto.
          apply Unnamed_thm1; auto.
        inversion H; subst.
        apply H2 in H0.
        inversion_clear H0.
        inversion_clear H4.
Admitted.
