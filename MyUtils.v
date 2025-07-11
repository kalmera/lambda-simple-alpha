Inductive slist (t:Type) := 
    |   snil : slist t
    |   snoc : slist t -> t -> slist t.

Arguments snil {t}%_type_scope.
Arguments snoc {t}%_type_scope _ _.

Module SListNotations.
Declare Scope snoc_scope.
Infix "::" := snoc (at level 60, right associativity) : snoc_scope.
Notation "[ ]" := snil (format "[ ]") : snoc_scope.
Notation "[ x ]" := (snoc snil x) : snoc_scope.
Notation "[ x ; y ; .. ; z ]" := (snoc .. (snoc (snoc snil x) y) .. z)
  (format "[ '[' x ; '/' y ; '/' .. ; '/' z ']' ]") : snoc_scope.
End SListNotations.

Import SListNotations.
Open Scope snoc_scope.

Fixpoint app [A : Type] (xs ys: slist A): slist A :=
    match ys with
    | snil => xs
    | snoc ys y => snoc (app xs ys) y
    end.

Notation "x ++ y" := (app x y).

Fixpoint length {A} (xs: slist A): nat :=
    match xs with 
    | snil => 0
    | snoc xs _ => S (length xs)
    end.

Fixpoint In {A} (a:A) (l:slist A) : Prop :=
    match l with
      | snil => False
      | snoc l' b  => b = a \/ In a l'
    end.

Fixpoint filter {A} (f: A -> bool) (l: slist A) :=
    match l with
    | snil => snil 
    | snoc l0 x => if f x then snoc (filter f l0) x else filter f l0
    end.

Inductive Forall {A : Type} (P : A -> Prop) : slist A -> Prop :=
      Forall_snil : Forall P snil
    | Forall_snoc : forall(x : A)(l : slist A), P x -> Forall P l -> Forall P (l::x).

Arguments Forall [A]%_type_scope P%_function_scope _%_snoc_scope.
Arguments Forall_snil [A]%_type_scope P%_function_scope.
Arguments Forall_snoc [A]%_type_scope [P]%_function_scope x [l]%_snoc_scope _ _.

Lemma in_app_iff {A} (l l' : slist A) (a : A): In a (l' ++ l) <-> In a l \/ In a l'.
Proof.
    split; intros.
    +   induction l; auto. inversion H; subst.
    ++  left. left. auto.   
    ++  simpl. destruct (IHl H0); tauto.
    +   destruct H; induction l; auto.
    ++  inversion H.
    ++  inversion H; subst; simpl; tauto.
    ++  right. auto.
Qed.

Lemma filter_In {A : Type} (f : A -> bool) (x : A) (l : slist A): In x (filter f l) <->
In x l /\ f x = true.
Proof.
    split; intros.
    +   induction l. 
    ++ inversion H. 
    ++  simpl in *. destruct (f t) eqn:E.
    +++ inversion H; subst; tauto.
    +++ destruct (IHl H). tauto.
    +   destruct H. induction l. 
    ++  inversion H.
    ++  inversion H; subst; simpl. 
    +++ rewrite H0. left. auto.
    +++ destruct (f t); auto. right. auto.
Qed.

Lemma app_assoc {A} (xs ys zs: slist A): (xs++ys)++zs = xs++(ys++zs).
Proof.
    induction zs; auto. cbn. rewrite IHzs. reflexivity.
Qed.

Lemma app_cons {A} (xs ys: slist A) v : (xs++ys)::v = xs++(ys::v).
Proof.
    induction ys; auto.
Qed.

Lemma length_app {A} (xs ys: slist A): length (xs++ys) = length ys + length xs.
Proof.
    induction ys; auto. cbn. rewrite IHys. reflexivity.
Qed. 

Lemma filter_app {A} p (xs ys: slist A): filter p (xs++ys) = filter p xs ++ filter p ys.
Proof.
    induction ys; auto. cbn. destruct (p t); rewrite IHys; auto.
Qed.

Lemma Forall_forall {A P} (l:slist A): Forall P l <-> (forall x, In x l -> P x).
Proof.
    split; intros.
    +   induction l; inversion H0. 
    ++  subst. inversion H; subst; auto. 
    ++  inversion H; subst. auto.
    +   induction l; constructor.
    ++  apply H. cbn. tauto.
    ++  apply IHl. intros. apply H. cbn. tauto.
Qed.

Lemma Forall_app {A P} (l1 l2:slist A): Forall P (l1++l2) <-> Forall P l1 /\ Forall P l2.
Proof.
    split; intros.
    +   induction l2; cbn in *.
    ++  split; auto. constructor.   
    ++  inversion H; subst. apply IHl2 in H3. 
        destruct H3. split; try tauto. constructor; auto.
    +   destruct H. induction l2; cbn in *; auto.
        inversion H0; subst. constructor; auto.
Qed.

Lemma app_nil {A} (xs: slist A): ([] ++ xs) = xs.
Proof.
    induction xs; auto. cbn. rewrite IHxs. auto.
Qed.

Theorem not_or_iff A B: ~(A \/ B) <-> ~A /\ ~B.
Proof. tauto. Qed.

Ltac inv c := inversion c; subst; clear c.

Class Monad@{d c} (m : Type@{d} -> Type@{c}) : Type :=
{ ret : forall {t : Type@{d}}, t -> m t
; bind : forall {t u : Type@{d}}, m t -> (t -> m u) -> m u
}.

Global Hint Mode Monad ! : typeclass_instances.

Declare Scope monad_scope.
Delimit Scope monad_scope with monad.

Notation "c >>= f" := (bind c f) (at level 58, left associativity) : monad_scope.
Notation "f =<< c" := (bind c f) (at level 61, right associativity) : monad_scope.

Notation "e1 ;; e2" := (bind e1%monad (fun _ => e2%monad))%monad
    (at level 61, right associativity) : monad_scope.

Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
    (at level 61, c1 at next level, right associativity) : monad_scope.

Notation "' pat <- c1 ;; c2" :=
    (bind c1 (fun x => match x with pat => c2 end))
    (at level 61, pat pattern, c1 at next level, right associativity) : monad_scope.

Definition M (ST:Type) (X:Type) : Type := 
    ST -> option X * ST.

Instance MMonad (ST:Type) : Monad (M ST) := {
    ret := fun {X} (x:X) (st:ST) => (Some x, st);
    bind := fun {X Y} f g (st:ST) =>
        match f st with 
        | (Some a, st') => g a st'
        | (None, st') => (None, st')
        end
}.


Ltac destruct_guard_in H :=
    generalize H; clear H;
    lazymatch goal with
    | |- context [match ?X with _ => _ end] => 
        let e := fresh "E" in destruct X eqn: e; 
            let h := fresh H in intros h
    | |- context [if ?X then _ else _] => 
        let e := fresh "E" in destruct X eqn: e; 
            let h := fresh H in intros h
    end.


Ltac destruct_guard :=
    match goal with
    | |- context [match ?X with _ => _ end] => 
        let e := fresh "E" in destruct X eqn: e
    | |- context [if ?X then _ else _] => 
        let e := fresh "E" in destruct X eqn: e
    end.

Open Scope monad_scope.

Definition fail {ST X} : M ST X :=
    fun st => (None, st).

Definition get_some {A} (f : option A) (P:f <> None): A.
Proof.
    destruct f. + exact a. + contradiction.
Defined.

Definition get_some_ind A (Q:A -> Prop) f P: (exists l, f = Some l /\ Q l) -> Q (@get_some A f P).
Proof.
    intros [l [H1 H2]]. subst. apply H2.
Defined.


Notation "x '∉' xs" := (~ In x xs)
    (at level 50, no associativity) : type_scope.
Notation "x '∈' xs" := (In x xs)
    (at level 50, no associativity) : type_scope.
Notation "xs '⊆' ys" := (Forall (fun x => x ∈ ys) xs)
    (at level 50, no associativity) : type_scope.


Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
    (at level 10, x binder, y binder, P at level 200,
    format "'[ ' '[ ' ∀ x .. y ']' , '/' P ']'") : type_scope.
Notation "∃ x .. y , P" := (exists x, .. (exists y, P) ..)
    (at level 10, x binder, y binder, P at level 200,
    format "'[ ' '[ ' ∃ x .. y ']' , '/' P ']'") : type_scope.
  
Notation "x ∨ y" := (x \/ y) (at level 85, right associativity) : type_scope.
Notation "x ∧ y" := (x /\ y) (at level 80, right associativity) : type_scope.
(* Notation "x → y" := (x -> y)
    (at level 99, y at level 200, right associativity): type_scope. *)
  
Notation "x ↔ y" := (x <-> y) (at level 95, no associativity): type_scope.
Notation "¬ x" := (~x) (at level 75, right associativity) : type_scope.
Notation "x ≠ y" := (x <> y) (at level 70) : type_scope.
  
Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
    (at level 10, x binder, y binder, t at level 200,
    format "'[ ' '[ ' 'λ' x .. y ']' , '/' t ']'").