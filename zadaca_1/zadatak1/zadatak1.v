(* a *)
Goal forall X Y, ~(X /\ Y) \/ (~X /\ Y) \/ (~X /\ ~Y) <-> ~(X /\ Y).
Proof.
  intros. split.
  - intros H G. destruct H.
    -- apply H. exact G.
    -- destruct H.
       --- apply H. apply G.
       --- apply H. apply G.
  - intros H. left. exact H.
Qed.

(* b *)
Goal forall X Y Z, ~(~X /\ Y /\ ~Z) /\ ~(X /\ Y /\ Z) /\ (X /\ ~Y /\ ~Z) <-> (X /\ ~Y /\ ~Z).
Proof.
  intros. split.
  - intros [H G]. destruct G. exact H1.
  - intros [H G]. destruct G. split.
    -- intros T. apply H0. apply T.
    -- split.
       --- intros D. apply H1. apply D.
       --- split.
           * exact H.
           * split. exact H0. exact H1.
Qed.






