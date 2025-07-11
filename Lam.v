From Stdlib Require Import Arith.
From Stdlib Require Import Recdef.
From Stdlib Require Import FunInd.
From Stdlib Require Import Nat.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.


Unset Allow StrictProp.  (* StrictProp not needed *)

(* UTF notations and few helper definitions *)
Require Import MyUtils.

Import SListNotations.
Open Scope snoc_scope.

(* Configuration module -- so we can run the implementation *)
Module Type LamConf.

Parameter V : Type.
Parameter eqvb : V -> V -> bool.
Parameter eqvb_reflect : ∀ x y, reflect (x = y) (eqvb x y).
Infix "=v?" := eqvb (at level 70) .

Parameter in_list: V -> slist V -> bool.

Parameter in_list_spec: ∀ x xs, reflect (In x xs) (in_list x xs).

Parameter var: nat -> V.
Parameter var_inj : ∀ x y, var x = var y <-> x=y. 

Parameter to_nat: V -> option nat.
Parameter to_nat_var: ∀ v n, to_nat v = Some n -> v = var n. 
Parameter to_nat_none: ∀ v, to_nat v = None -> ∀ n, v <> var n. 

End LamConf.


(* Specification overview *)
Module Type LamSpec (Import C:LamConf).

(* 
    Basic Definition 
*)
Inductive Lam : Type :=
    | Var   : V -> Lam 
    | App   : Lam -> Lam -> Lam 
    | Abs   : V -> Lam -> Lam
.

Fixpoint FV (t:Lam) : slist V :=
    match t with 
    | Var v => [v]
    | App f u => FV f ++ FV u
    | Abs x u => filter (fun y => negb (x =v? y)) (FV u)
    end
.

Fixpoint Vars (t:Lam) : slist V :=
    match t with 
    | Var v => [v]
    | App f u => Vars f ++ Vars u
    | Abs x u => (Vars u) :: x
    end
.

Fixpoint height (t:Lam) : nat :=
    match t with 
    | Var v => 1
    | App f u => 1 + max (height f) (height u)
    | Abs x u => 1 + height u
    end
.

(* disable warning for now -- I actually would like to set the 
   level to 0 but somehow Rocq parses it wrong then. *)
Local Set Warnings "-closed-notation-not-level-0".

(* 
    Definition of (generic) alpha-equivalence for variables
*)
Reserved Notation "❬ xs ;  x ❭ =vα ❬ ys ;  y ❭" (at level 60).

Inductive VarAlpha : slist V -> slist V -> V -> V -> Prop :=
| GlobalVA x: ❬[];x❭ =vα ❬[];x❭ 
| HereVA s l x y : ❬s::x;x❭ =vα ❬l::y;y❭
| ThereVA s l x y a b : x <> a -> y <> b -> ❬s; x❭ =vα ❬l; y❭ -> ❬s::a; x❭ =vα ❬l::b; y❭
where "❬ s ; x ❭ =vα ❬ l ; y ❭" := (VarAlpha s l x y) .

(* 
    Definition of (generic) alpha-equivalence for terms
*)
Reserved Notation "❬ xs ; x ❭ =α ❬ ys ; y ❭" 
    (at level 60, format "'❬' xs ';'  x '❭'  '=α'  '❬' ys ';'  y '❭'").

Inductive Alpha : slist V -> slist V -> Lam -> Lam -> Prop :=
  | VarA s l x y: ❬s;x❭ =vα ❬l;y❭ -> ❬s; Var x❭ =α ❬l; Var y❭
  | AppA s l f g t u: ❬s; f❭ =α ❬l; g❭ -> ❬s; t❭ =α ❬l; u❭ -> ❬s; App f t❭ =α ❬l; App g u❭
  | AbsA s l x y t u: ❬s::x; t❭ =α ❬l::y; u❭ -> ❬s; Abs x t❭ =α ❬l; Abs y u❭
where "❬ s ; x ❭ =α ❬ l ; y ❭" := (Alpha s l x y) .

(*  Normal alpha-equivalence *)
Notation "t '=α' u" := (❬[];t❭ =α ❬[];u❭) (at level 60).

(* Generic Alpha is an equivalence relation: *)
Parameter AlphaRefl: ∀ a xs, ❬xs; a❭ =α ❬xs;a❭.
Parameter AlphaSym: ∀ a b xs ys, ❬xs; a❭ =α ❬ys; b❭ -> ❬ys; b❭ =α ❬xs; a❭.
Parameter AlphaTrans: ∀ a b c xs ys zs,  ❬xs;a❭ =α ❬ys;b❭ -> ❬ys;b❭ =α ❬zs;c❭ -> ❬xs;a❭=α❬zs;c❭ .

(* Free variables of alpha-equivalent terms are same *)
Parameter AlphaFV: ∀ t t', t =α t' -> (FV t) = (FV t').

(* Barendregt&Barendsen style compatibility rules:
*)
Parameter AlphaConvAppR: ∀ m m' z, m =α m' -> App m z =α App m' z.
Parameter AlphaConvAppL: ∀ m m' z, m =α m' -> App z m =α App z m'.
Parameter AlphaConvAbs:  ∀ m m' x, m =α m' -> Abs x m =α Abs x m'.


(* Making implicit globals explicit or explicit globals implicit *)
Parameter AlphaCtxImplGlobs: ∀ t t' xs ys zs,
    length xs = length ys -> 
    ❬xs;t❭ =α ❬ys;t'❭ <-> ❬zs++xs;t❭ =α ❬zs++ys;t'❭.

(* Removing of shadowed variables *)
Parameter AlphaRemShadowed:
    ∀ t xs3 ys3 u x y y' xs2 xs1 ys2 ys1,
    length xs3 = length ys3 ->
    length xs2 = length ys2 ->
    ❬xs1 ++ [x] ++ xs2 ++ [x] ++ xs3;t❭ =α ❬ys1 ++ [y'] ++ ys2 ++ [y] ++ ys3; u❭ ->
    ❬xs1 ++ xs2 ++ [x] ++ xs3; t❭ =α ❬ys1 ++ ys2 ++ [y] ++ ys3; u❭.

(* Some more structural rules *)
Parameter AlphaCtxWeaken:
    ∀ u u' xs xs' ys ys' v y,
    length xs = length ys ->
    ❬xs' ++ xs; u❭ =α ❬ys' ++ ys; u'❭ ->
    (v ∉ FV u \/ v ∈ xs) /\ (y ∉ FV u' \/ y ∈ ys) -> 
    ❬xs' ++ [v] ++ xs; u❭ =α ❬ys' ++ [y] ++ ys; u'❭.

Parameter AlphaSwap:
    ∀ t xs ys u v x y b xs' ys',
    length xs = length ys ->
    ❬xs' ++ [v; x] ++ xs; t❭ =α ❬ys' ++ [b; y] ++ ys; u❭ ->
    v <> x -> b <> y -> 
    ❬xs' ++ [x; v] ++ xs; t❭ =α ❬ys' ++ [y; b] ++ ys; u❭.
    

(* 
    Definition and properties of substitutions
*)

(* non-capture-avoiding substitution -- as a function *)
Fixpoint ssubst (t:Lam) (x:V) (u:Lam) : Lam :=
    match t with 
    | Var v   => if v =v? x then u else Var v
    | App f v => App (ssubst f x u) (ssubst v x u) 
    | Abs y v => if y =v? x then Abs y v else Abs y (ssubst v x u)
    end.

Reserved Notation "t '⎡' y '→' u '⎤' '~' v" 
    (at level 60, format "t '⎡' y '→' u '⎤'  '~'  v").

(* capture-avoiding substitution -- as a relation *)
Inductive Subst (y:V) (u:Lam) : Lam -> Lam -> Prop :=
    | SubstVarEq: (Var y)⎡y→u⎤ ~ u
    | SubstVarNeq x: x<>y -> (Var x)⎡y→u⎤ ~ (Var x)
    | SubstApp f f' t t': f⎡y→u⎤~f' -> t⎡y→u⎤~t' -> (App f t)⎡y→u⎤~(App f' t')
    | SubstAbsEq t: (Abs y t)⎡y→u⎤ ~ (Abs y t)
    | SubstAbsNF x t t' : x <> y -> x ∉ FV u -> t⎡y→u⎤ ~ t' -> (Abs x t)⎡y→u⎤ ~ (Abs x t')
    | SubstAbsA x z t t' t'' : x<>y -> x ∈ FV u -> z ∉ Vars u -> z ∉ Vars t -> z <> x -> z <> y -> 
        t⎡x→Var z⎤~t' -> t'⎡y→u⎤ ~ t'' -> Abs x t⎡y→u⎤ ~ Abs z t''
where "t ⎡ y → u ⎤ ~ v" := (Subst y u t v).


(* Barendregt&Barendsen style alpha-rule: *)
Parameter SubstFreshVarAlpha:
    ∀ u v x y,
    y ∉ Vars u -> u ⎡ x → Var y ⎤ ~ v -> Abs x u =α Abs y v.

Parameter AlphaSubstUnusedVar:
    ∀ t y u v, y ∉ FV t -> t⎡y→u⎤ ~ v -> t =α v.

(* All substitution results are (simple) alpha-equivalent  *)
Parameter SubstAlpha_Simple: 
    ∀ t x u v v', 
    t⎡ x → u ⎤ ~ v ->
    t⎡ x → u ⎤ ~ v' ->
    v =α v'.

(* General alpha-equivalence of substitution. *)
Parameter SubstAlpha:
    ∀ t t' u u' v v' xs ys x y ,
    ❬xs; u❭ =α ❬ys; u'❭ -> 
    ❬xs; Abs x t❭ =α ❬ys; Abs y t'❭ -> 
    t ⎡ x → u ⎤ ~ v ->
    t' ⎡ y → u' ⎤ ~ v' -> 
    ❬xs; v❭ =α ❬ys; v'❭.

(* One of the main (and most difficult) substitution properties.  *)
Parameter SubstAlphaMain:
    ∀ t t' u u' v v' xs ys x y xs' ys',
    length xs' = length ys' ->
    x ∉ xs' -> y ∉ ys' ->
    ❬xs++xs';u❭ =α ❬ys++ys';u'❭ ->
    ❬xs++[x]++xs'; t❭ =α ❬ys++[y]++ys'; t'❭ ->
    t ⎡ x → u ⎤ ~ v -> 
    t' ⎡ y → u' ⎤ ~ v' -> 
    ❬xs++xs'; v❭ =α ❬ys++ ys'; v'❭.
    
(* The substitution lemma.  *)
Parameter SubstSwap:
    ∀ t1 t2 t3 u1 u2 x y u1' t2' t3',
    x ≠ y -> x ∉ FV u2 ->
    t1⎡ x → u1 ⎤ ~ t2 -> t2⎡ y → u2 ⎤ ~ t3 ->
    u1⎡ y → u2 ⎤ ~ u1' ->
    t1⎡ y → u2 ⎤ ~ t2' -> t2'⎡ x → u1' ⎤ ~ t3' ->
    t3 =α t3'.

(* 
    Implementation of capture-avoiding substitutions using a monad
*)

Definition fresh : M nat V :=
    fun st => (Some (var st), S st).

Fixpoint subst' (g:nat) (t:Lam) (x:V) (u:Lam) : M nat Lam :=
    match g with 
    | 0 => fail
    | S g => 
    match t with 
    | Var v =>  
        if v =v? x then 
            ret u
        else 
            ret (Var v)
    | App f v => 
        f' <- subst' g f x u ;;
        v' <- subst' g v x u ;;
        ret (App f' v') 
    | Abs y v => 
        if y =v? x then 
            ret (Abs y v)
        else if in_list y (FV u) then 
            z <- fresh ;;
            v' <- subst' g v y (Var z) ;;
            v' <- subst' g v' x u ;;
            ret (Abs z v')
        else 
            v' <- subst' g v x u ;;
            ret (Abs y v')
    end
    end.

Definition varToOrZero (v: V): nat :=
    match to_nat v with
    | None => 0
    | Some b => b
    end.

Fixpoint termMaxVar (t: Lam): nat :=
    match t with 
    | Var v => varToOrZero v
    | App f u => max (termMaxVar f) (termMaxVar u)
    | Abs x u => max (varToOrZero x) (termMaxVar u)
    end.

Fixpoint termListMaxVar (xs:slist Lam): nat :=
    match xs with 
    | [] => 0
    | xs::x => max (termListMaxVar xs) (termMaxVar x)
    end.

Fixpoint varListMaxVar (vs: slist V): nat :=
    match vs with 
    | [] => 0
    | xs::x => max (varListMaxVar xs) (varToOrZero x)
    end.

(* subst' terminates for these arguments *)
Parameter substTerm: ∀ t x u,
    fst (subst' (height t) t x u (1+termListMaxVar [Var x; u; t])) <> None.

(* The substitution function -- main work is done by subst' *)
Definition subst t x u :=
    get_some
    (fst (subst' (height t) t x u (1+termListMaxVar [Var x; u; t])))
    (substTerm t x u).

(* Specification: subst returns a substitution *)
Parameter substSpec: ∀ t x u, t⎡x → u⎤ ~ subst t x u.

(* 
    Decision proc. of alpha-equivalence
*)

Fixpoint decVarAlpha xs ys x y : bool :=
match xs, ys with
| xs'::x', ys'::y' =>
    match x =v? x', y =v? y' with
    | true, true => true
    | false, false => decVarAlpha xs' ys' x y 
    | _, _ => false
    end
| [], [] => x =v? y
| _, _ => false
end.

Fixpoint decAlpha xs ys x y :=
match x, y with
| Var x, Var y => decVarAlpha xs ys x y
| App f1 t1, App f2 t2 => decAlpha xs ys f1 f2 && decAlpha xs ys t1 t2
| Abs a t1, Abs b t2 => decAlpha (xs::a) (ys::b) t1 t2
| _, _ => false
end.

(* Specification: dec(Var)Alpha returns true iff alpha-equivalent *)
Parameter VarAlpha_spec: 
    ∀ xs ys x y , decVarAlpha xs ys x y = true <-> ❬ xs; x ❭ =vα ❬ ys; y ❭.

Parameter decAlphaSpec: 
    ∀ t u xs ys, decAlpha xs ys t u = true <-> ❬xs;t❭ =α ❬ys;u❭.

(* 
    Barendregt Variable Condition 
*)
Inductive BVC ts: Lam -> Prop :=
    | BVCVar v: BVC ts (Var v)
    | BVCApp f t: BVC ts f -> BVC ts t -> BVC ts (App f t)
    | BVCAbs v t: ~In v ts -> BVC ts t -> BVC ts (Abs v t)
    .

(* "BVC ts t" means that t does not contain elements of ts 
    as local variables. *)
Parameter BVCprop:
    ∀ t x v ts, 
    x ∈ ts -> Forall (fun v => v ∈ ts) (FV v) ->
    BVC ts t -> t ⎡ x → v ⎤ ~ ssubst t x v.

Parameter BVCssubst:
    ∀ t x ts v,
    BVC ts v -> BVC ts t -> 
    BVC ts (ssubst t x v).

(* a well known property of ssubst *)
Parameter ssubst_swap:
    ∀ t  x y u1 u2 ,
    x <> y -> BVC [y] t -> x ∉ FV u2 ->
    ssubst (ssubst t x u1) y u2 = ssubst (ssubst t y u2) x (ssubst u1 y u2).

(* 
    Barendregt Variable Condition refresh 
    
    "bvcRefresh t ts" returns a term t' such that 
        * t' =α t
        * BVC [ y | x ∈ ts, y ∈ FV(x)] t'
*)

Fixpoint bvcRefresh' (g:nat) (t:Lam) ts : M nat Lam :=
    match g with 
    | 0 => fail
    | S g => 
    match t with
    | Var x => ret (Var x)
    | App f u => 
        f' <- bvcRefresh' g f ts ;;
        u' <- bvcRefresh' g u ts ;;
        ret (App f' u')
    | Abs y u =>
        if in_list y ts then 
            y' <- fresh;;
            u' <- subst' g u y (Var y')  ;;
            u'' <-  bvcRefresh' g u' ts ;;
            ret (Abs y' u'')
        else
            u' <- bvcRefresh' g u ts;;
            ret (Abs y u')
    end
    end.


Parameter bvcRefreshTerm: ∀ t xs,
  let r := bvcRefresh' (height t) t xs (1 + max (varListMaxVar xs) (termMaxVar t)) 
  in fst r <> None.

Definition bvcRefresh t xs :=
  let r := bvcRefresh' (height t) t xs (1 + max (varListMaxVar xs) (termMaxVar t)) 
  in get_some (fst r) (bvcRefreshTerm t xs).

Parameter bvcRefreshAlpha: 
    ∀ t vs, t =α (bvcRefresh t vs) .

Parameter bvcRefreshProp:
    ∀ t vs,
    BVC vs (bvcRefresh t vs).

End LamSpec.


Module Lam (C:LamConf) <: LamSpec (C).
Import C.

Lemma eqvb_refl: ∀ y, y =v? y = true .
Proof.
    intros. destruct (eqvb_reflect y y); auto.
Qed.

Lemma eqvb_neq: ∀ x y, x =v? y = false <-> x<>y .
Proof.
    intros. destruct (eqvb_reflect x y); split; intros; try contradiction; auto. inv H.
Qed.

Inductive Lam : Type :=
    | Var   : V -> Lam 
    | App   : Lam -> Lam -> Lam 
    | Abs   : V -> Lam -> Lam
    .

Fixpoint FV (t:Lam) : slist V :=
    match t with 
    | Var v => [v]
    | App f u => FV f ++ FV u
    | Abs x u => filter (fun y => negb (x =v? y)) (FV u)
    end
.

Fixpoint Vars (t:Lam) : slist V :=
    match t with 
    | Var v => [v]
    | App f u => Vars f ++ Vars u
    | Abs x u => (Vars u) :: x
    end
.

Fixpoint height (t:Lam) : nat :=
    match t with 
    | Var v => 1
    | App f u => 1 + max (height f) (height u)
    | Abs x u => 1 + height u
    end
.

Lemma HeightNot0 t : height t <> 0.
Proof.
    induction t; auto; simpl; lia.
Qed.

Lemma VarsAbsFV: ∀ t x, In x (FV t) -> In x (Vars t).
Proof.
    induction t; simpl; intros; auto.
    +   apply in_app_iff in H. apply in_app_iff . destruct H; auto. 
    +   apply filter_In in H. destruct H.
        right. apply IHt, H. 
Qed. 

Reserved Notation "t '⎡' y '→' u '⎤' '~' v" 
    (at level 60, format "t '⎡' y '→' u '⎤'  '~'  v").

(* capture-avoiding substitution -- as a relation *)
Inductive Subst (y:V) (u:Lam) : Lam -> Lam -> Prop :=
    | SubstVarEq: (Var y)⎡y→u⎤ ~ u
    | SubstVarNeq x: x<>y -> (Var x)⎡y→u⎤ ~ (Var x)
    | SubstApp f f' t t': f⎡y→u⎤~f' -> t⎡y→u⎤~t' -> (App f t)⎡y→u⎤~(App f' t')
    | SubstAbsEq t: (Abs y t)⎡y→u⎤ ~ (Abs y t)
    | SubstAbsNF x t t' : x <> y -> x ∉ FV u -> t⎡y→u⎤ ~ t' -> (Abs x t)⎡y→u⎤ ~ (Abs x t')
    | SubstAbsA x z t t' t'' : x<>y -> x ∈ FV u -> z ∉ Vars u -> z ∉ Vars t -> z <> x -> z <> y -> 
        t⎡x→Var z⎤ ~ t' -> t'⎡y→u⎤ ~ t'' -> Abs x t⎡y→u⎤ ~ Abs z t''
where "t '⎡' y '→' u '⎤' '~' v" := (Subst y u t v).


Lemma SubstHeight : ∀ t t' x y ,
    t⎡x → Var y⎤ ~ t' ->
    height t = height t'.
Proof.
    intros. remember (Var y) as u.
    generalize dependent y. 
    induction H; intros; subst; simpl; auto.
    +   erewrite IHSubst1; [|reflexivity]. 
        erewrite IHSubst2; [|reflexivity].
        lia. 
    +   erewrite IHSubst; [|reflexivity]. auto. 
    +   erewrite IHSubst1; [|reflexivity]. 
        erewrite IHSubst2; [|reflexivity].
        lia. 
Qed.

Set Warnings "-closed-notation-not-level-0".

Reserved Notation "❬ xs ;  x ❭ =vα ❬ ys ;  y ❭" (at level 60).

Inductive VarAlpha : slist V -> slist V -> V -> V -> Prop :=
    | GlobalVA x: ❬[];x❭ =vα ❬[];x❭ 
    | HereVA s l x y : ❬s::x;x❭ =vα ❬l::y;y❭
    | ThereVA s l x y a b : x <> a -> y <> b -> ❬s; x❭ =vα ❬l; y❭ -> ❬s::a; x❭ =vα ❬l::b; y❭
where "❬ s ; x ❭ =vα ❬ l ; y ❭" := (VarAlpha s l x y) .

Reserved Notation "❬ xs ; x ❭ =α ❬ ys ; y ❭" 
    (at level 60, format "'❬' xs ';'  x '❭'  '=α'  '❬' ys ';'  y '❭'").

Inductive Alpha : slist V -> slist V -> Lam -> Lam -> Prop :=
    | VarA s l x y: ❬s;x❭ =vα ❬l;y❭ -> ❬s; Var x❭ =α ❬l; Var y❭
    | AppA s l f g t u: ❬s; f❭ =α ❬l; g❭ -> ❬s; t❭ =α ❬l; u❭ -> ❬s; App f t❭ =α ❬l; App g u❭
    | AbsA s l x y t u: ❬s::x; t❭ =α ❬l::y; u❭ -> ❬s; Abs x t❭ =α ❬l; Abs y u❭
where "❬ s ; x ❭ =α ❬ l ; y ❭" := (Alpha s l x y) .
  
Notation "t '=α' u" := (Alpha [] [] t u) (at level 60).

Lemma VarAlphaInv: ∀ xs ys t t', Alpha xs ys (Var t) (Var t') -> VarAlpha xs ys t t'.
Proof. intros. inv H. auto. Qed.


Theorem VarAlphaRefl: 
    ∀ a xs, VarAlpha xs xs a a.
Proof. 
    intros. induction xs; [constructor|].
    destruct (eqvb_reflect t a); subst; constructor; auto.
Qed.


Property AlphaRefl: 
    ∀ a xs, Alpha xs xs a a.
Proof.
    induction a; intros.
    +   constructor. apply VarAlphaRefl.
    +   constructor; auto.
    +   constructor; auto.
Qed.

Property VarAlphaSym: 
    ∀ a b xs ys,  
        VarAlpha xs ys a b -> VarAlpha ys xs b a.
Proof.
    intros. induction H; constructor; auto.
Qed.

Property AlphaSym: 
    ∀ a b xs ys,  
        Alpha xs ys a b -> Alpha ys xs b a.
Proof.
    induction a; intros.
    +   inv H. constructor. apply VarAlphaSym, H3.
    +   inv H.
        constructor; auto.
    +   inv H. constructor. auto.
Qed.

Theorem AlphaTrans: 
    ∀ a b c xs ys zs,
    Alpha xs ys a b -> 
    Alpha ys zs b c -> 
    Alpha xs zs a c.
Proof.
    induction a; intros.
    +   inv H. inv H0. constructor.
        generalize dependent zs.
        generalize dependent y0.
        induction H4; intros.
    ++  inv H3. constructor.
    ++  inv H3.
    +++ constructor.
    +++ contradiction.
    ++  inv H3.
    +++ contradiction.
    +++ constructor; auto.
    +   inv H. inv H0. constructor.
    ++  eapply IHa1; eauto.
    ++  eapply IHa2; eauto.
    +   inv H. inv H0.
        constructor. eapply IHa; eauto.
Qed.

Lemma AlphaRemShadowed:
    ∀ t xs3 ys3 u x y y' xs2 xs1 ys2 ys1,
    length xs3 = length ys3 ->
    length xs2 = length ys2 ->
    ❬xs1 ++ [x] ++ xs2 ++ [x] ++ xs3;t❭ =α ❬ys1 ++ [y'] ++ ys2 ++ [y] ++ ys3; u❭ ->
    ❬xs1 ++ xs2 ++ [x] ++ xs3; t❭ =α ❬ys1 ++ ys2 ++ [y] ++ ys3; u❭.
Proof.
    intros t. induction t.
    +   intros xs3. induction xs3; intros. {
            destruct ys3; [|inv H]. cbn in *. inv H1.
            constructor. generalize dependent ys2.
            induction xs2; intros.
            *   destruct ys2; [|inv H0].
                cbn in *. inv H5; constructor; auto.
                inv H10; try contradiction; auto.   
            *   destruct ys2; [inv H0|]. cbn in *.
                inv H5; constructor; auto.
                inv H10; constructor; auto. clear IHxs2.
                generalize dependent ys2. induction xs2; intros. {
                    destruct ys2; [|inv H0]. cbn in *.
                    inv H12; auto. contradiction.
                }
                destruct ys2; [inv H0|]. cbn in *.
                inv H12; constructor; auto. 
        }
        destruct ys3; [inv H|]. cbn in *.
        inv H1. inv H5; do 2 constructor; auto.
        assert (W1:❬ xs1 ++ [x] ++ xs2 ++ [x] ++ xs3; Var v ❭ =α ❬ ys1 ++ [y'] ++ ys2 ++ [y] ++ ys3; Var y0 ❭). {
            constructor; auto.
        }
        eapply IHxs3 in W1; auto. 
        inv W1. auto.
    +   intros. inv H1. constructor.
    ++  eapply IHt1; eauto.
    ++  eapply IHt2; eauto.
    +   intros. inv H1. constructor.
        replace ((xs1 ++ xs2 ++ [x] ++ xs3) :: v )
            with (xs1 ++ xs2 ++ [x] ++ (xs3 :: v)) by auto.
        replace ((ys1 ++ ys2 ++ [y] ++ ys3) :: y0) 
            with (ys1 ++ ys2 ++ [y] ++ (ys3 :: y0)) by auto.
        eapply IHt; simpl in *; eauto. 
Qed.


Lemma AlphaCtxWeaken:
    ∀ u u' xs xs' ys ys' v y,
    length xs = length ys ->
    ❬xs' ++ xs; u❭ =α ❬ys' ++ ys; u'❭ ->
    (v ∉ FV u \/ v ∈ xs) /\ (y ∉ FV u' \/ y ∈ ys) -> 
    ❬xs' ++ [v] ++ xs; u❭ =α ❬ys' ++ [y] ++ ys; u'❭.
Proof.
    induction u; intros.
    +   inv H0. simpl in *.
        rewrite not_or_iff in H1, H1.
        destruct H1 as [[[H0 _]| H0] [[H1 _]|H1]]. 
    ++  constructor.
        generalize dependent ys. 
        induction xs; intros; destruct ys; try (inv H; fail).
    +++ constructor; auto.
    +++ inv H5; [constructor|].
        simpl. constructor; auto.
    ++  generalize dependent ys.
        induction xs; intros. { destruct ys; [|inv H].  inv H1. }
        destruct ys; [inv H|].
        cbn in H, H1, H5 |- *. inv H5. { do 2 constructor. }
        destruct H1.
    +++ subst. clear IHxs.
        generalize dependent ys.
        induction xs; intros. { 
            destruct ys; [|inv H]. cbn in H10. 
            cbn. do 2 constructor; auto.
            constructor; auto.
        }
        destruct ys; [inv H|].
        cbn in H, H11 |- *.
        inv H11. { do 2 constructor; auto. constructor. }
        do 2 constructor; auto. constructor; auto.
        apply IHxs in H12; [|lia].
        inv H12. inv H6; auto. contradiction. 
    +++ subst. clear IHxs.
        generalize dependent ys.
        induction xs; intros. { 
            destruct ys; [|inv H].    
            inv H1. 
        }
        destruct ys; [inv H|].
        cbn in H1, H11 |- *.
        inv H11. { do 2 constructor; auto. constructor. }
        do 2 constructor; auto. constructor; auto.
        destruct H1. { 
            subst. clear IHxs.
            generalize dependent ys.
            induction xs; intros. { 
                destruct ys; [|inv H]. cbn. constructor; auto.
            }
            destruct ys; [inv H|].
            cbn in H13 |- *. 
            inv H13. { constructor; auto.  }
            constructor; auto.
        }
        apply IHxs in H13; auto.
        inv H13. inv H8; auto. contradiction.
    ++  generalize dependent ys.
        induction xs; intros. { destruct ys; [|inv H]. cbn in H0. inv H0. }
        destruct ys; [inv H|].
        cbn in H, H0, H5 |- *. inv H5. { do 2 constructor. }
        destruct H0.
    +++ subst. clear IHxs.
        generalize dependent ys.
        induction xs; intros. { 
            destruct ys; [|inv H]. cbn in H10. 
            cbn. do 2 constructor; auto.
            constructor; auto.
        }
        destruct ys; [inv H|].
        cbn in H, H11 |- *.
        inv H11. { do 2 constructor; auto. constructor. }
        do 2 constructor; auto. constructor; auto.
        apply IHxs in H12; [|lia].
        inv H12. inv H6; auto. contradiction. 
    +++ subst. clear IHxs.
        generalize dependent ys.
        induction xs; intros. { 
            destruct ys; [|inv H]. inv H0. 
        }
        destruct ys; [inv H|].
        cbn in H, H11 |- *.
        inv H11. { do 2 constructor; auto. constructor. }
        do 2 constructor; auto. constructor; auto.
        cbn in H0. destruct H0. { subst.
            clear IHxs.
            generalize dependent ys.
            induction xs; intros. { 
                destruct ys; [|inv H]. cbn. constructor; auto.
            }
            destruct ys; [inv H|].
            cbn in H13 |- *. 
            inv H13. { constructor; auto.  }
            constructor; auto.
        }
        apply IHxs in H13; auto.
        inv H13. inv H8; auto. contradiction.
    ++  generalize dependent ys.
        generalize dependent v0.
        induction xs; intros. { destruct ys; [|inv H]. cbn in H0. inv H0. }
        destruct ys; [inv H|].
        cbn in H, H0, H1, H5 |- *. 
        destruct H0, H1.
    +++ inv H5.
        *   do 2 constructor.
        *   do 2 constructor; auto.
            clear IHxs.
            generalize dependent ys.
            induction xs; intros. { 
                destruct ys; [|inv H]. cbn in H11 |- *. 
                constructor; auto.
            }
            destruct ys; [inv H|].
            cbn in H, H11 |- *.
            inv H11. { do 2 constructor; auto. }
            constructor; auto.
    +++ subst. clear IHxs.
        inv H5. { do 2 constructor. }
        do 2 constructor; auto.
        generalize dependent ys.
        induction xs; intros. { 
            destruct ys; [|inv H]. inv H1.
        }
        destruct ys; [inv H|].
        cbn in H, H1, H10 |- *.
        destruct H1.
        *   subst. inv H10. { do 2 constructor. }
            constructor; auto.
            clear IHxs.
            generalize dependent ys.
            induction xs; intros. { 
                destruct ys; [|inv H]. cbn in *. 
                constructor; auto.
            }
            destruct ys; [inv H|].
            cbn in H, H11 |- *.
            inv H11. { constructor.  }
            constructor; auto.
        *   inv H10. { constructor. }
            constructor; auto.
        +++ inv H5.
            *   do 2 constructor.
            *   do 2 constructor; auto.
                clear IHxs.
                generalize dependent ys.
                induction xs; intros. { 
                    destruct ys; [|inv H]. cbn in H11 |- *. 
                    constructor; auto.
                }
                destruct ys; [inv H|].
                cbn in H, H11 |- *.
                inv H11. { do 2 constructor; auto. }
                constructor; auto.
                cbn in H0.
                destruct H0.
            **  subst.
                clear IHxs.
                generalize dependent ys.
                induction xs; intros. { 
                    destruct ys; [|inv H]. cbn in H12 |- *. 
                    constructor; auto.
                }
                destruct ys; [inv H|].
                cbn in H, H12 |- *.
                inv H12. { do 2 constructor; auto. }
                constructor; auto.
            **  apply IHxs; auto.
        +++ inv H5. { do 2 constructor. }
            do 2 constructor; auto.
            eapply IHxs in H11; eauto.
            inv H11. auto.
    +   inv H0. simpl in H1.
        rewrite in_app_iff, not_or_iff in H1, H1.
        constructor.
    ++  eapply IHu1; auto. tauto.
    ++  eapply IHu2; auto. tauto.
    +   inv H0. simpl in H1.
        rewrite filter_In in H1, H1.
        constructor.
        replace ((xs' ++ [v0] ++ xs) :: v) with (xs' ++ [v0] ++ (xs :: v)) by auto.
        replace ((ys' ++ [y] ++ ys) :: y0) with (ys' ++ [y] ++ (ys :: y0)) by auto.
        apply IHu; auto; [cbn; lia|].
        cbn. 
        assert ((negb true = true) <-> False). { split; intros; inv H0. }
        assert (∀ Q, Q /\ False <-> False ). { split; intros; inv H2. inv H4. }
        destruct (eqvb_reflect v v0), (eqvb_reflect y0 y); subst; try tauto.
Qed.

Lemma AlphaCtxWeakenLeft:
    ∀ u u' xs' ys'  v y,
    Alpha xs' ys' u u' ->
    ~ In v (FV u) -> ~ In y (FV u')  ->
    Alpha (xs'::v) (ys' :: y) u u'.
Proof.
    intros.
    apply AlphaCtxWeaken with (xs:=[]) (ys:=[]); auto.
Qed.

Lemma SubstFreshVarAlpha':
    ∀ u v x y xs ys,
    x ∉ ys -> y ∉ ys -> y ∉ Vars u ->
    u ⎡ x → Var y ⎤ ~ v ->
    Alpha ((xs :: x) ++ ys) ((xs :: y) ++ ys) u v.
Proof.
    induction u; intros t x y xs ys  Hxys Hyys Hyu H.
    +   simpl in Hyu.
        apply not_or_iff in Hyu. destruct Hyu as [Hyu _].
        inv H.
    ++  constructor.  induction ys; cbn in *; [constructor|]. 
        apply not_or_iff in Hxys, Hyys. destruct Hxys, Hyys. 
        constructor; auto. 
    ++  constructor.  induction ys; cbn in *; [constructor; auto;apply VarAlphaRefl|].
        rewrite not_or_iff in Hxys, Hyys.
        destruct (eqvb_reflect v t); subst;
        constructor; try tauto.
    +   simpl in Hyu. rewrite in_app_iff in Hyu.
        apply not_or_iff in Hyu. destruct Hyu as [Hyu1 Hyu2].
        inv H. constructor.
    ++  eapply IHu1; auto.
    ++  eapply IHu2; auto.
    +   simpl in Hyu.
        rewrite not_or_iff in Hyu. destruct Hyu. inv H.
    ++  constructor.
        replace (((xs :: v) ++ ys) :: v)
            with (xs ++ [v] ++ (ys :: v)) by (rewrite <-app_assoc; auto). 
        replace (((xs :: y) ++ ys) :: v)
            with (xs ++ [y] ++ (ys :: v)) by (rewrite <-app_assoc; auto).
        eapply (AlphaCtxWeaken u u (ys::v) xs (ys::v) xs v y) ; auto. 
        { apply AlphaRefl. }
        cbn. split; try tauto.
        left. intro C. apply VarsAbsFV in C. auto.  
    ++  constructor.
        replace (((xs :: x) ++ ys) :: v) with ((xs :: x) ++ (ys :: v)) by auto.
        replace (((xs :: y) ++ ys) :: v) with ((xs :: y) ++ (ys :: v)) by auto.
        eapply IHu with (ys:=ys::v); auto.
    +++ intros C. inv C; contradiction.
    +++ intros C. inv C; contradiction.
    ++  simpl in H5. destruct H5; [|destruct H]. subst.
         contradiction.
Qed.

Theorem SubstFreshVarAlpha:
    ∀ u v x y,
    y ∉ Vars u -> u⎡x→Var y⎤ ~ v -> Abs x u =α Abs y v.
Proof.
    intros.
    constructor.
    eapply SubstFreshVarAlpha' with (ys:=[]) (xs:=[]) in H0; auto.
Qed. 

Theorem AlphaConvAppR m m' z:
    Alpha [] [] m m' -> Alpha [] [] (App m z) (App m' z).
Proof.
    intros. constructor; auto. apply AlphaRefl.
Qed.

Theorem AlphaConvAppL m m' z:
    Alpha [] [] m m' -> Alpha [] [] (App z m) (App z m').
Proof.
    intros. constructor; auto. apply AlphaRefl.
Qed.

Theorem AlphaCtxImplGlobs: ∀ m m' xs ys zs,
    length xs = length ys -> ❬xs;m❭ =α ❬ys;m'❭ <-> ❬zs ++ xs;m❭ =α ❬zs ++ ys;m'❭.
Proof.
    intros m m' xs ys zs Hl. split.
    +   intro H. clear Hl. induction H; intros; constructor; auto.
        induction H; simpl; try (constructor; auto; fail).
        induction zs; [constructor|].
        destruct (eqvb_reflect t x); subst; constructor; auto.
    +   generalize dependent m'.
        generalize dependent xs.
        generalize dependent ys.
        induction m; intros.
    ++  inv H. constructor.
        generalize dependent ys.
        induction xs; intros. { destruct ys; [|inv Hl].
            cbn in *. induction zs; auto.
            inv H3; [constructor|auto].
        }
        destruct ys; [inv Hl|]. inv H3; [constructor|].
        constructor; auto.
    ++  inv H. constructor.
    +++ eapply IHm1; eauto.  
    +++ eapply IHm2; eauto.
    ++ inv H. constructor. eapply IHm; cbn; eauto.
Qed.    

Theorem AlphaCtxStrenghtenRight: ∀ m xs ys zs m' ,
    length xs = length ys ->
    Alpha (zs++xs) (zs++ys) m m' -> Alpha xs ys m m'.
Proof.
    induction m; intros.
    +   inv H0. constructor. generalize dependent ys.
        induction xs; intros. { destruct ys; [|inv H].
            cbn in *. induction zs. { inv H4. constructor. }
            inv H4; [constructor|auto].
        }
        destruct ys; [inv H|]. inv H4; [constructor|].
        constructor; auto.
    +   inv H0. constructor.
    ++  eapply IHm1; eauto.  
    ++  eapply IHm2; eauto.
    +   inv H0. constructor. eapply IHm; cbn; eauto.
Qed.  
  


Theorem AlphaConvAbs m m' x:
    Alpha [] [] m m' -> Alpha [] [] (Abs x m) (Abs x m').
Proof.
    intros. constructor.
    apply (AlphaCtxImplGlobs _ _ [] []); auto.
Qed.

Lemma SubstVarNotIn:
    ∀ t t' y v z,
    ~ In y (FV t) ->
    z<>y ->
    t ⎡ v → Var z ⎤ ~ t' ->
    ~ In y (FV t').
Proof.
    intro t. remember (height t) as g.
    assert (g >= height t) by lia. clear Heqg.
    generalize dependent t.
    induction g. {
        intros. pose proof (HeightNot0 t). lia.
    }
    destruct t; intros Hh t' y u z Hyt Hu H; simpl in Hh, H.
    +   inv H; auto.
        simpl in *.
        apply not_or_iff in Hyt as [Hyt _].
        apply not_or_iff. split; auto.
    +   inv H. simpl in *.
        rewrite in_app_iff in Hyt.
        apply not_or_iff in Hyt as [Hyt1 Hyt2 ].
        rewrite in_app_iff.
        apply not_or_iff. split.
    ++  eapply IHg in H4; eauto. lia.
    ++  eapply IHg in H2; eauto. lia.
    +   inv H; cbn in *.
    ++  rewrite filter_In.
        rewrite filter_In in Hyt.
        destruct (eqvb_reflect v y).
    +++ intros [_ C]. inv C.
    +++ intros [C _]. apply Hyt. split; auto.
    ++  rewrite filter_In.
        rewrite filter_In in Hyt.
        destruct (eqvb_reflect v y).
    +++ intros [_ C]. inv C.
    +++ intros [C _].
        eapply IHg in H5; eauto. lia.
    ++  rewrite filter_In.
        rewrite filter_In in Hyt.
        destruct H3; auto. subst.
        apply not_or_iff in H4 as [H4 _].
        destruct (eqvb_reflect z0 y).
    +++ intros [_ C]. inv C.
    +++ intros [C _].
        apply SubstHeight in H8 as W1.
        eapply IHg in H10; eauto; [lia|].
        eapply IHg in H8; eauto; [lia|].
        intro E.
        apply Hyt. split; auto.
        destruct (eqvb_reflect v y); auto.
Qed.

Lemma AlphaSubstUnusedVar:
    ∀ t' y u' v',
    ~(In y (FV t')) -> 
    t'⎡ y → u' ⎤ ~ v' ->
    t' =α v'.
Proof.
    intro t. remember (height t) as g.
    assert (g >= height t) by lia. clear Heqg.
    generalize dependent t.
    induction g. {
        intros. pose proof (HeightNot0 t). lia.
    }
    destruct t; intros Hh y u' v' H H0; simpl in Hh, H.
    +   inv H0. 
    ++  destruct H. constructor. auto.
    ++  do 2 constructor. 
    +   inv H0. simpl in H.
        rewrite in_app_iff, not_or_iff in H.
        destruct H. constructor.
    ++  eapply IHg; eauto. lia.
    ++  eapply IHg; eauto. lia.
    +   rewrite filter_In in H.
        destruct (eqvb_reflect v y).
    ++  subst. inv H0; try contradiction.
        constructor.
        apply (AlphaCtxImplGlobs _ _ [] []); auto.
        apply AlphaRefl.
    ++  simpl in H.
        assert (~ (In y (FV t))). {
            intro C. apply H. split; auto.
        }
        clear H. inv H0; try contradiction.
    +++ constructor.
        apply (AlphaCtxImplGlobs _ _ [] []); auto.
        eapply IHg; eauto. lia. 
    +++ constructor.
        apply SubstHeight in H9 as W1.
        eapply IHg in H11 as W2; [| lia |].
        *   eapply AlphaConvAbs with (x:=z) in W2.
            inv W2. eapply AlphaTrans; eauto.
            eapply SubstFreshVarAlpha in H9; auto.
            inv H9. auto.
        *   eapply SubstVarNotIn in H8; eauto.
Qed.


Inductive FVCtx : slist V -> slist V -> slist V -> slist V -> Prop :=
    | FVCNil xs ys: FVCtx xs ys [] []
    | FVCEq xs: FVCtx [] [] xs xs
    | FVCCons x xs y ys qs ws: 
        VarAlpha xs ys x y ->
        FVCtx xs ys qs ws ->
        FVCtx xs ys (qs::x) (ws::y)
    .

Lemma FVCtxApp: 
    ∀ xs ys qs qs',
    FVCtx xs ys qs qs' ->
    ∀ ws ws',
    FVCtx xs ys ws ws' ->
    FVCtx xs ys (ws++qs) (ws'++qs').
Proof.
    intros xs ys qs qs' H.
    induction H; cbn; intros; auto.
    +   induction xs; auto.
        inv H; cbn in *; repeat constructor. auto.
    +   constructor; auto.
Qed.

Lemma FVCtxFilter:
    ∀ t u0 v xs y ys,
    FVCtx (xs::v) (ys::y) t u0 ->
    FVCtx xs ys (filter (fun y0 : V => negb (v =v? y0)) t) (filter (fun y0 : V => negb (y =v? y0)) u0).
Proof.
    induction t; intros.
    +   inv H. cbn. constructor.
    +   inv H. inv H4.
    ++  cbn. do 2 rewrite eqvb_refl. cbn.
        apply IHt, H6.  
    ++  cbn.
        apply not_eq_sym in H3, H8.
        apply eqvb_neq in H3, H8.
        rewrite H3, H8. cbn.
        constructor; auto.
Qed.


Lemma AlphaToFVC: 
    ∀ t u xs ys,
    Alpha xs ys t u -> FVCtx xs ys (FV t) (FV u).
Proof.
    induction t; intros.
    +   inv H. cbn. induction H3.
    ++  constructor.
    ++  do 2 constructor. 
    ++  eapply FVCCons; auto.
    +++ constructor; auto.
    +++ constructor.
    +   inv H. cbn. apply  FVCtxApp.
    ++  apply IHt2, H6.
    ++  apply IHt1, H4.
    +   inv H. cbn.
        apply FVCtxFilter, IHt, H5 .
Qed.


Lemma FVCtxNotIn:
    ∀ xs ys ws qs,
    FVCtx xs ys ws qs ->
    ∀ x y,
    VarAlpha xs ys x y ->
    ~(In x ws) -> ~(In y qs).
Proof.
    intros xs ys ws qs H.
    induction H;intros.
    +   intro C; inv C.
    +   inv H. auto.
    +   cbn in H2. rewrite not_or_iff in H2. destruct H2.
        cbn. intro C. destruct C; subst.
    ++  clear IHFVCtx H3 H0. 
        induction H; inv H1; try contradiction.
        auto.
    ++  eapply IHFVCtx; eauto. 
Qed. 

Lemma AlphaNotFree:
    ∀ t u x y xs ys xs' ys',
    length xs' = length ys' ->
    ~In x xs' -> 
    ~In y ys' -> 
    ~(In x (FV t)) ->
    Alpha ((xs::x)++xs') ((ys::y)++ys') t u ->
    ~(In y (FV u)). 
Proof.
    intros.
    apply AlphaToFVC in H3.
    eapply FVCtxNotIn in H3; eauto.
    clear H3. 
    generalize dependent ys'.
    induction xs'; intros. { 
        destruct ys'; [|inv H]. constructor.
    }
    destruct ys'; [inv H|]. cbn in *.
    apply not_or_iff in H0 as [W1 W2].
    apply not_or_iff in H1 as [W3 W4].
    constructor; auto.
Qed.



Lemma AlphaSwap:
    ∀ t xs ys u v x y b xs' ys',
    length xs = length ys ->
    ❬xs' ++ [v; x] ++ xs; t❭ =α ❬ys' ++ [b; y] ++ ys; u❭ ->
    v <> x -> b <> y -> 
    ❬xs' ++ [x; v] ++ xs; t❭ =α ❬ys' ++ [y; b] ++ ys; u❭.
Proof.
    induction t; intros.
    +   inv H0. constructor.
        generalize dependent ys. 
        induction xs; intros.
    ++  destruct ys; [|inv H]. cbn in *.
        inv H6. { constructor; auto. constructor. }
        inv H11. { do 2 constructor. }
        constructor; auto.
        constructor; auto.
    ++  destruct ys; [inv H|]. cbn in *.
        inv H6. { do 2 constructor. }
        constructor; auto. 
    +   inv H0. constructor.
    ++  apply IHt1; auto.
    ++  apply IHt2; auto.
    +   inv H0. constructor.
        replace ((xs' ++ [x; v0] ++ xs) :: v) with (xs' ++ [x; v0] ++ (xs :: v)) by auto.
        replace ((ys' ++ [y; b] ++ ys) :: y0) with (ys' ++ [y; b] ++ (ys :: y0)) by auto.
        apply IHt; auto. cbn. lia.
Qed.

Corollary AlphaSwap_simple:
    ∀ t u0 v x y y0 xs ys,
    Alpha ((xs::x)::v) ((ys::y)::y0) t u0 ->
    v <> x -> y0 <> y ->
    Alpha ((xs::v)::x) ((ys::y0)::y) t u0.
Proof.
    intros. apply AlphaSwap with (xs:=[]) (ys:=[]); auto.
Qed.

Theorem SubstAlphaMain:
    ∀ t t' u u' v v' xs ys x y xs' ys',
    length xs' = length ys' ->
    ~ In x xs' -> ~ In y ys' ->
    ❬xs++xs';u❭ =α ❬ys++ys';u'❭ ->
    ❬xs++[x]++xs'; t❭ =α ❬ys++[y]++ys'; t'❭ ->
    t ⎡ x → u ⎤ ~ v -> 
    t' ⎡ y → u' ⎤ ~ v' -> 
    ❬xs++xs'; v❭ =α ❬ys++ ys'; v'❭.
Proof.
    intro t. remember (height t) as g.
    assert (g >= height t) by lia. clear Heqg.
    generalize dependent t.
    induction g. {
        intros. pose proof (HeightNot0 t). lia.
    }
    destruct t; intros; simpl in H.
    +   inv H4. clear IHg H.
        inv H5; inv H6; auto.
    ++  exfalso. clear H3 H2. 
        generalize dependent ys'.
        induction xs'. { 
            intros. destruct ys'; [|inv H0]. 
            cbn in *. inv H10; try contradiction.
        }
        intros. destruct ys'; [inv H0|].
        cbn in H1.
        apply not_or_iff in H1 as [W1 W2].
        cbn in H10. inv H10; try contradiction.
        eapply IHxs' in H9; auto.
    ++  exfalso. clear H3 H1. 
        generalize dependent ys'.
        induction xs'. { 
            intros. destruct ys'; [|inv H0]. 
            cbn in *. inv H10; try contradiction.
        }
        intros. destruct ys'; [inv H0|].
        cbn in H2.
        apply not_or_iff in H2 as [W1 W2].
        cbn in H10. inv H10; try contradiction.
        eapply IHxs' in H9; auto.
    ++  constructor. clear H3.
        generalize dependent ys'.
        induction xs'. { 
            intros. destruct ys'; [|inv H0]. 
            cbn in *. inv H10; try contradiction.
            auto.
        }
        intros. destruct ys'; [inv H0|].
        cbn in H2, H1.
        apply not_or_iff in H1 as [W1 W2].
        apply not_or_iff in H2 as [W3 W4].
        cbn in H10. inv H10; try contradiction.
    +++ constructor.
    +++ cbn. constructor; auto.
    +   inv H4. inv H5. inv H6.
        constructor.
    ++  eapply IHg in H11; eauto. lia.
    ++  eapply IHg in H13; eauto. lia.
    +   inv H4. inversion H5; subst.
    ++  assert (❬(xs::v) ++ xs'; Abs v t❭ =α ❬(ys::y) ++ ys'; Abs y0 u0❭). {
            do 2 rewrite <- app_assoc in H12.
            constructor.  auto.
        }
        apply AlphaNotFree in H4; auto;
            [|  cbn;
                rewrite filter_In; intros [_ C];
                rewrite eqvb_refl in C; inv C].
        eapply AlphaSubstUnusedVar in H4; eauto.
        inv H4. constructor.
        eapply AlphaCtxImplGlobs in H13; auto. cbn in H13.
        eapply AlphaTrans; [|apply H13].
        eapply (AlphaRemShadowed t [] []) in H12; auto.
    ++  inv H6.
    +++ assert (Alpha ((xs::x)++xs') ((ys::y0)++ys') (Abs v t) (Abs y0 u0)). {
            do 2 rewrite <- app_assoc in H12.
            constructor. auto.
        }
        apply AlphaSym in H4.
        apply AlphaNotFree in H4; auto;
            [|  cbn; rewrite filter_In; intros [_ C];
                rewrite eqvb_refl in C; inv C] . 
        eapply AlphaSubstUnusedVar in H5; eauto.
        inv H5. constructor.
        eapply AlphaCtxImplGlobs in H13; auto. cbn in H13.
        eapply AlphaSym in H13.
        eapply AlphaTrans; [apply H13|].
        eapply AlphaSym in H12.
        eapply (AlphaRemShadowed _ [] [] ) in H12; auto.
        eapply AlphaSym in H12. apply H12.
    +++ constructor.
        do 2 rewrite app_cons.
        eapply IHg; eauto; cbn; try lia.
        *   apply not_or_iff. split; auto.
        *   apply not_or_iff. split; auto.
        *   apply AlphaCtxWeakenLeft; auto.
        *   apply H12.
    +++ constructor.
        do 2 rewrite app_cons.
        eapply IHg; eauto; cbn; try lia.
        *   apply not_or_iff. split; auto.
        *   apply not_or_iff. split; auto.
        *   apply AlphaCtxWeakenLeft; auto.
            intro C. apply VarsAbsFV in C. contradiction.
        *   eapply AlphaTrans; eauto.
            apply SubstFreshVarAlpha in H18; auto. inv H18.
            eapply AlphaCtxImplGlobs in H19; auto. apply H19.
    ++  inv H6.
    +++ assert (❬((xs ::x) ++ xs'); Abs v t❭ =α ❬((ys :: y0) ++ ys') ; Abs y0 u0❭). {
            do 2 rewrite <- app_assoc in H12.
            constructor. auto.
        }
        apply AlphaSym in H4.
        apply AlphaNotFree in H4; auto;
            [|  cbn; rewrite filter_In; intros [_ C];
                rewrite eqvb_refl in C; inv C] . 
        eapply AlphaSubstUnusedVar in H4; eauto.
        inv H4. constructor.
        eapply AlphaCtxImplGlobs in H18; auto. cbn in H18.
        eapply AlphaSym in H18.
        eapply AlphaTrans; [apply H18|].
        eapply AlphaSym in H12.
        eapply (AlphaRemShadowed _ [] []) in H12; auto.
        eapply AlphaSym in H12. apply H12.
    +++ constructor.
        do 2 rewrite app_cons.
        eapply IHg; eauto; cbn; try lia.
        *   apply SubstHeight in H15 . lia.
        *   apply not_or_iff. split; auto.
        *   apply not_or_iff. split; auto.
        *   apply AlphaCtxWeakenLeft; auto.
            intro C. apply VarsAbsFV in C. contradiction.
        *   eapply AlphaTrans; eauto.
            apply SubstFreshVarAlpha in H15; auto. inv H15.
            eapply AlphaCtxImplGlobs in H19; auto. 
            apply AlphaSym, H19.
    +++ constructor.
        do 2 rewrite app_cons.
        eapply IHg; eauto; cbn; try lia.
        *   apply SubstHeight in H15 . lia.
        *   apply not_or_iff. split; auto.
        *   apply not_or_iff. split; auto.
        *   apply AlphaCtxWeakenLeft; auto.
        **  intro C. apply VarsAbsFV in C. contradiction.
        **  intro C. apply VarsAbsFV in C. contradiction.
        *   apply SubstFreshVarAlpha in H23; auto. inv H23.
            eapply AlphaCtxImplGlobs in H24; auto.
            eapply AlphaTrans; [|apply H24].
            eapply AlphaTrans; eauto.
            apply SubstFreshVarAlpha in H15; auto. inv H15.
            eapply AlphaCtxImplGlobs in H23; auto. 
            apply AlphaSym, H23.
Qed.

Lemma app_mid_app_app {A} (xs ys: slist A) x : 
    ((ys :: x) ++ xs) = ((ys ++ [x]) ++ xs).
Proof.
    induction xs; auto. 
Qed.

Theorem Contraction:
    ∀ t xs x1 x2 xs2 ys y1 y2 ys2 t' v v',
    length xs = length ys ->
    x1 ∉ xs -> y1 ∉ ys ->
    x2 ∉ ([x1]++xs) -> y2 ∉ ([y1]++ys) ->
    ❬xs2 ++ [x2; x1] ++ xs; t❭ =α ❬ys2 ++ [y2; y1] ++ ys; t'❭ ->
    t ⎡ x2 → Var x1 ⎤ ~ v -> 
    t' ⎡ y2 → Var y1 ⎤ ~ v' -> 
    ❬xs2 ++ [x1] ++ xs; v❭ =α ❬ys2 ++ [y1] ++ ys; v'❭.
Proof.
    intros.
    rewrite (app_mid_app_app xs), (app_mid_app_app ys) in H4|-*.
    rewrite app_assoc in H4, H4.
    eapply SubstAlphaMain; cbn; eauto. { do 2 rewrite length_app. cbn. lia. }
    clear -H0 H1 H.
    generalize dependent ys.
    induction xs; intros. { destruct ys; [|inv H]. cbn in *. do 2 constructor. }
    destruct ys; [inv H|]. cbn in *.
    apply not_or_iff in H0, H1. destruct H0, H1.
    do 2 constructor; auto.
    apply VarAlphaInv, IHxs; auto.
Qed.



Corollary SubstAlpha:
    ∀ t t' u u' v v' xs ys x y ,
    Alpha xs ys u u' ->
    Alpha xs ys (Abs x t) (Abs y t') ->
    t⎡ x → u  ⎤ ~ v  ->
    t'⎡ y → u' ⎤ ~ v' ->
    Alpha xs ys v v'.
Proof.
    intros. inv H0. eapply SubstAlphaMain with (xs':=[]) (ys':=[]); auto; cbn; eauto.
Qed.

Corollary SubstAlpha_Simple: 
    ∀ t x u v v', 
    t⎡ x → u ⎤ ~ v ->
    t⎡ x → u ⎤ ~ v' ->
    v =α v'.
Proof.
    intros. eapply (SubstAlpha t t u u v v'); eauto.
    + apply AlphaRefl.
    + apply AlphaRefl.   
Qed.

(* ? *)
Corollary Substitutivity :
    ∀ t x u u' v v',
    u =α u' ->
    t⎡ x → u ⎤ ~ v ->
    t⎡ x → u' ⎤ ~ v' ->
    v =α v'.
Proof.
    intros. eapply SubstAlpha; eauto. apply AlphaRefl. 
Qed.

(* ? *)
Corollary Congruence : 
    ∀ t t' u v v' xs ys x y xs' ys',
    length xs' = length ys' ->
    x ∉ xs' -> y ∉ ys' ->
    ❬xs++xs'; u❭ =α ❬ys++ys'; u❭ ->
    ❬xs++[x]++xs'; t❭ =α ❬ys++[y]++ys'; t'❭ ->
    t⎡x→u⎤ ~ v -> t'⎡y→u⎤ ~ v' -> ❬xs++xs'; v❭ =α ❬ys++ys'; v'❭.
Proof.
    intros. eapply SubstAlphaMain; eauto.
Qed.

Lemma Filter_negb_in_list:
    ∀ xs ys a,
    filter (λ y0 : V, negb (in_list y0 (ys::a))) xs =  filter (λ y0 : V, negb (a =v? y0 )) (filter (λ y0 : V, negb (in_list y0 ys)) xs).
Proof.
    induction xs; intros; cbn; auto.
    destruct (in_list_spec t (ys::a)); cbn.
    +   destruct (in_list_spec t ys); cbn.
    ++  rewrite IHxs. auto.
    ++  inv i; try contradiction. 
        rewrite eqvb_refl. cbn.
        rewrite IHxs. auto.
    +   destruct (in_list_spec t ys).
    ++  exfalso. apply n. cbn. tauto.
    ++  cbn in *. apply not_or_iff in n as [H _].
        destruct (eqvb_reflect a t); subst; try contradiction. cbn.
        rewrite IHxs. auto. 
Qed.

Lemma filter_swap {A}:
    ∀ (xs:slist A) p q, filter p (filter q xs) = filter q (filter p xs).
Proof.
    induction xs; intros; auto. cbn. 
    destruct_guard; cbn; destruct_guard; rewrite IHxs; auto; cbn; rewrite E; auto.
Qed.


Lemma AlphaFV':
    ∀ t t' xs ys,
        Alpha xs ys t t' -> filter (fun y => negb (in_list y xs)) (FV t) = filter (fun y => negb (in_list y ys)) (FV t').
Proof.
    induction t; intros.
    +   inv H. induction H3.
    ++  cbn. destruct (in_list_spec x []); auto.
    ++  cbn. 
        assert (x ∈ (s :: x)). { cbn. tauto. }
        assert (y ∈ (l :: y)). { cbn. tauto. }
        destruct (in_list_spec x (s::x)); try contradiction.
        destruct (in_list_spec y (l::y)); try contradiction.
        auto.
    ++  do 2 rewrite Filter_negb_in_list.
        rewrite IHVarAlpha.
        clear -H H0 H3.
        cbn. destruct_guard.
    +++ cbn. induction H3.
        * apply not_eq_sym, eqvb_neq in H, H0. rewrite H, H0. auto.
        * destruct (in_list_spec y (l :: y)); [inv E|].
            exfalso. apply n. cbn. tauto.
        *   apply IHVarAlpha; auto.
            destruct (in_list_spec y l); auto.
            destruct (in_list_spec y (l::b0)); auto.
            exfalso. apply n. cbn. tauto.
    +++ auto.
    +   inv H. cbn. do 2 rewrite filter_app.
        erewrite IHt1; eauto.
        erewrite IHt2; eauto.
    +   inv H. cbn.
        rewrite filter_swap, (filter_swap (FV u)).
        eapply IHt in H5 as Q.
        do 2 rewrite Filter_negb_in_list in Q.
        apply Q.
Qed.

Lemma AlphaFV:
    ∀ t t',
        t =α t' -> (FV t) = (FV t').
Proof.
    intros. 
    eapply AlphaFV' in H.
    revert H. generalize (FV t'). generalize (FV t).
    induction s; intros; cbn in *. 
    +   destruct s; auto. cbn in H.
        destruct (in_list_spec v []).
    ++ inv i.
    ++ inv H.
    +   destruct (in_list_spec t0 []); [inv i|].
        cbn in H. destruct s0.
    ++  cbn in H. inv H.
    ++  cbn in H.
        destruct (in_list_spec v []); [inv i|].
        cbn in H. inv H. f_equal. apply IHs. auto.
Qed.



Definition fresh : M nat V :=
    fun st => (Some (var st), S st).

Fixpoint subst' (g:nat) (t:Lam) (x:V) (u:Lam) : M nat Lam :=
    match g with 
    | 0 => fail
    | S g => 
    match t with 
    | Var v =>  
        if v =v? x then 
            ret u
        else 
            ret (Var v)
    | App f v => 
        f' <- subst' g f x u ;;
        v' <- subst' g v x u ;;
        ret (App f' v') 
    | Abs y v => 
        if y =v? x then 
            ret (Abs y v)
        else if in_list y (FV u) then 
            z <- fresh ;;
            v' <- subst' g v y (Var z) ;;
            v' <- subst' g v' x u ;;
            ret (Abs z v')
        else 
            v' <- subst' g v x u ;;
            ret (Abs y v')
    end
    end.


Lemma SubstIncreasesM : ∀ g t x u st o st',
    subst' g t x u st = (o, st') ->
    st' >= st.
Proof.
    induction g; simpl; intros. { inv H. auto. }
    destruct t.
    +   destruct (eqvb_reflect v x). { inv H.  auto. }
        inv H. lia.
    +   destruct_guard_in H.
        apply IHg in E.
        destruct o0.
    ++  destruct_guard_in H.
        apply IHg in E0.
        destruct o0; inv H; lia.
    ++  inv H. auto.
    +   destruct (eqvb_reflect v x). { inv H.  auto. }
        destruct_guard_in H.
    ++  destruct_guard_in H.
        apply IHg in E0. destruct o0.
    +++ destruct_guard_in H.
        apply IHg in E1. destruct o0; inv H; lia.
    +++ inv H; lia.
    ++  destruct_guard_in H.
        apply IHg in E0. destruct o0; inv H; lia.
Qed.

Definition FreshState n t := 
    ∀ v, v >= n -> ~ (In (var v) (Vars t)). 

Lemma InVarsApp: ∀ v f t,
    In v (Vars (App f t)) <-> 
    In v (Vars t) \/ In v (Vars f).
Proof.
    intros. split; intros; simpl in H; apply in_app_iff, H.
Qed.

Lemma InVarsAbs: ∀ v x t,
    In v (Vars (Abs x t)) <-> 
    x = v \/ In v (Vars t).
Proof.
    intros. simpl. tauto.
Qed.

Lemma FreshStateApp: ∀ n f x,
    FreshState n (App f x) <->
    FreshState n x /\ FreshState n f.
Proof.
    intros. unfold FreshState in *. split; intros H.
    +   split; intros v H0 C; eapply (H v H0); simpl; 
        apply in_app_iff; tauto.
    +   intros v H0 C. apply InVarsApp in C.
        destruct H, C; [eapply (H v)| eapply (H1 v)]; auto.
Qed.

Lemma FreshStateAbs: ∀ n y t,
    FreshState n (Abs y t) <->
    (∀ v, v >= n -> y <> var v ) /\ FreshState n t.
Proof.
    intros. unfold FreshState in *. simpl in *. split; intros.
    +   split; intros v H0 C; eapply (H v H0); tauto.
    +   intros C. destruct H, C; [eapply (H v) | eapply (H1 v)]; auto.
Qed.

Lemma FreshStateLeq: ∀ n t n',
    n' >= n ->
    FreshState n t -> FreshState n' t.
Proof.
    unfold FreshState. intros. apply H0. lia.
Qed.

Ltac solve_fs :=
try (
        try assumption;
        try match goal with
        | H: subst' _ _ _ _ _ = (Some _, _) |- _ =>
            let W := fresh "W" in
            apply SubstIncreasesM in H as W
        end;
        repeat match goal with
        | H : FreshState _ _ |- In _ (Vars _) -> False =>
            apply H
        | H : FreshState _ _ |- FreshState _ _ => 
            unshelve (eapply (FreshStateLeq _ _ _ _ H));auto
        | |- FreshState _ (Var _) =>
            unfold FreshState; simpl; intros;
            let C := fresh "C" in (intros [C|[]];
            eapply var_inj in C; destruct C; lia)
        | |- FreshState (S _) _ =>
            eapply FreshStateLeq
        end; 
        try lia;
        fail
).

Lemma  substFreshState: ∀ g t x u st o st',
    FreshState st t ->
    FreshState st u ->
    subst' g t x u st = (Some o, st') ->
    FreshState st' o .
Proof.
    induction g; simpl; intros t x u st o st' Ht Hu H v L. { inv H. }
    destruct t.
    +   destruct (eqvb_reflect v0 x); inv H; auto.
    +   destruct_guard_in H.
        destruct o0; [|inv H].
        destruct_guard_in H.
        destruct o0; inv H.
        apply FreshStateApp in Ht as [Ht1 Ht2].
        unfold not. rewrite InVarsApp, Decidable.not_or_iff.
        apply SubstIncreasesM in E as W.
        apply SubstIncreasesM in E0 as W1.
        split.
    ++  eapply (IHg t2 x u n _ st'); auto;
        eapply (FreshStateLeq st); auto; lia.
    ++  eapply (IHg t1 x u st _ n); auto. lia.
    +   apply FreshStateAbs in Ht as [Ht1 Ht2].   
        destruct (eqvb_reflect v0 x); inv H.
    ++  unfold not. rewrite InVarsAbs, Decidable.not_or_iff.
        split; [ apply Ht1 | apply Ht2 ]; auto.
    ++  destruct_guard_in H1.
    +++ destruct_guard_in H1.
        destruct o0; [|inv H1].
        destruct_guard_in H1.
        destruct o0; inv H1.
        apply SubstIncreasesM in E0 as W1.
        apply SubstIncreasesM in E1 as W2.
        unfold not. rewrite InVarsAbs, Decidable.not_or_iff.
        split. { 
            intros. apply var_inj in H. subst. lia.
        } 
        eapply IHg in E0; solve_fs.
        eapply IHg in E1; solve_fs.
    +++ destruct_guard_in H1.
        destruct o0; inv H1. unfold not.
        rewrite InVarsAbs, Decidable.not_or_iff.
        split; eapply IHg in E0 as R; solve_fs.
        intro C. subst.
        eapply Ht1; [|reflexivity].
        apply SubstIncreasesM in E0; lia.
Qed.


Lemma substHeight : ∀ g t x v n t' n0 ,
    subst' g t x (Var v) n = (Some t', n0) ->
    height t = height t'.
Proof.
    induction g; intros. { inv H. }
    cbn in H. destruct t.
    +   destruct_guard_in H; inv H; auto.
    +   destruct_guard_in H.
        destruct_guard_in H; [|inv H]. 
        destruct_guard_in H.
        destruct_guard_in H; [|inv H].
        inv H. cbn.
        apply IHg in E, E1. lia.
    +   destruct_guard_in H; [inv H; auto|].
        destruct_guard_in H. 
    ++  destruct_guard_in H.
        destruct_guard_in H; [|inv H].
        destruct_guard_in H.
        destruct_guard_in H; [|inv H].
        inv H. cbn. apply IHg in E1, E3. lia.
    ++  destruct_guard_in H.
        destruct_guard_in H; [|inv H].
        inv H. cbn. apply IHg in E1. lia.
Qed.

Theorem substTermEx g : ∀ t x u st,
    g >= height t ->
    fst (subst' g t x u st) <> None.
Proof.
    induction g; intros t x u st  H C; simpl. 
    { pose proof (HeightNot0 t). lia. }
    destruct t; simpl in C, H.
    +   destruct (eqvb_reflect v x); simpl; auto; inv C.
    +   destruct_guard_in C.
        destruct o; [ destruct_guard_in C; destruct o|];
        try (inv C; fail).
    ++  eapply (IHg t2 x u n);
        try eapply FreshStateLeq; solve_fs; try lia.
        rewrite E0. auto.
    ++  eapply (IHg t1 x u st); solve_fs.
        rewrite E. auto.
    +   destruct (eqvb_reflect v x); simpl; auto; [inv C|].
        destruct_guard_in C.
    ++  destruct_guard_in C.
        apply SubstIncreasesM in E0 as T.
        destruct o; [destruct_guard_in C; destruct o|]; inv C.
    +++ apply substHeight in E0 as R.
        eapply (IHg l x u n0); 
        try eapply FreshStateLeq; solve_fs; try lia.
        rewrite E1. auto.
    +++ eapply (IHg t v (Var (var st)) (S st)); try lia.
        rewrite E0. auto.
    ++  destruct_guard_in C.
        destruct o; inv C.
        eapply IHg; [|rewrite E0]; auto. lia.
Qed. 

Definition varToOrZero (v: V): nat :=
    match to_nat v with
    | None => 0
    | Some b => b
    end.

Fixpoint termMaxVar (t: Lam): nat :=
    match t with 
    | Var v => varToOrZero v
    | App f u => max (termMaxVar f) (termMaxVar u)
    | Abs x u => max (varToOrZero x) (termMaxVar u)
    end.

Fixpoint termListMaxVar (xs:slist Lam): nat :=
    match xs with 
    | [] => 0
    | xs::x => max (termListMaxVar xs) (termMaxVar x)
    end.

Fixpoint varListMaxVar (vs: slist V): nat :=
    match vs with 
    | [] => 0
    | xs::x => max (varListMaxVar xs) (varToOrZero x)
    end.

Lemma MaxVarsFresh: ∀ t a,
    FreshState (1 + max a (termMaxVar t)) t.
Proof.
    induction t; intros a n H.
    +   simpl in *. unfold varToOrZero in H. destruct (to_nat v) eqn:E.
    ++  apply to_nat_var in E. subst. intro C.
        destruct C; [|inv H0].  apply var_inj in H0.  lia.
    ++  intro C. destruct C; [|inv H0]. eapply to_nat_none; eauto.
    +   unfold not. rewrite InVarsApp, Decidable.not_or_iff.
        simpl in H.
        split; [eapply (IHt2 a) | eapply (IHt1 a)]; lia.
    +   simpl in H.
        unfold not. unfold varToOrZero in H. rewrite InVarsAbs, Decidable.not_or_iff.
        destruct (to_nat v) eqn:E.
    ++  apply to_nat_var in E. subst. 
        split.
    +++ intro H0. apply var_inj in H0. subst. lia. 
    +++ eapply (IHt a).  lia.
    ++  split.
    +++ eapply to_nat_none in E. apply E.
    +++ eapply IHt; eauto.  
Qed.


Lemma substEnoughGas': ∀ g g' t x z st, 
    g >= g' ->
    g' >= height t ->
    subst' g' t x z st = subst' (height t) t x z st.
Proof.
    induction g; intros.
    +   pose proof (HeightNot0 t). lia.
    +   pose proof (HeightNot0 t). 
        destruct g'; [lia|].
        destruct t; cbn in H.
    ++  cbn. auto.
    ++  cbn in H0 |- *.
        rewrite IHg; try lia.
        destruct (subst' (height t1) t1 x z st) eqn:E1.
        rewrite (IHg _ t1); try lia.
        rewrite E1.
        rewrite IHg; try lia.
        destruct (subst' (height t2) t2 x z n) eqn:E2.
        rewrite IHg; try lia.
        rewrite E2. 
        reflexivity.
    ++  cbn in H0 |- *.
        destruct (v =v? x) eqn:E1; auto.
        destruct (in_list_spec v (FV z)).
    +++ rewrite IHg; try lia.
        destruct (subst' (height t) t v (Var (var st)) (S st)) eqn:E3.
        destruct o; auto.
        apply substHeight in E3 as E4.
        rewrite IHg; try lia.
        rewrite E4. reflexivity.
    +++ rewrite IHg; try lia.
        destruct (subst' (height t) t x z st) ; auto.
Qed.


Lemma substEnoughGas: ∀ g t x z st, 
    g >= height t ->
    subst' g t x z st = subst' (height t) t x z st.
Proof.
    intros. eapply substEnoughGas'; auto.
Qed.


Theorem SubstImpl t: ∀ n u v y,
    FreshState n (Var y) ->
    FreshState n t ->
    FreshState n u ->
    fst (subst' (height t) t y u n) = Some v ->
    t⎡y → u⎤~ v.
Proof.
    remember (height t) as g.
    assert (g >= height t) by lia. clear Heqg.
    generalize dependent t.
    induction g; intros. {
        simpl in H3. inv H3.
    }
    destruct t; intros.
    + simpl in H3. destruct (eqvb_reflect v0 y); inv H3.
    ++ constructor 1.
    ++ constructor 2. auto.
    +   apply FreshStateApp in H1 as [Ht1 Ht2].
        simpl in H, H3.
        destruct_guard_in H3.
        destruct_guard_in H3; [|inv H3].
        destruct_guard_in H3.
        destruct_guard_in H3; inv H3.
        constructor; auto.
    ++  eapply IHg with (n:=n); auto; [lia|].
        rewrite E. auto.
    ++  apply SubstIncreasesM in E.
        eapply IHg with (n:=n0); auto; solve_fs.
        rewrite E1. auto.
    +   simpl in H.
        apply FreshStateAbs in H1 as [Hv Ht].
        simpl in H3.  destruct (eqvb_reflect v0 y); [inv H3|]. {
            constructor.
        }
        destruct_guard_in H3.
    ++  destruct_guard_in H3.
        destruct_guard_in H3; [|inv H3].
        destruct_guard_in H3.
        destruct_guard_in H3; inv H3.
        econstructor; auto.
    +++ destruct (in_list_spec v0 (FV u)); auto. inv E.
    +++ intro C. eapply Hv; auto.
    +++ intro C. eapply (H0 n); cbn; auto.
    +++ eapply IHg with (n:= S n); solve_fs.
        *   intro. intros. cbn. intros [C |[]]. subst.
            eapply Hv; try reflexivity. lia. 
        *   rewrite E0. simpl. eauto.
    +++ apply SubstIncreasesM in E0 as W1.
        apply substFreshState in E0 as W2; solve_fs.
        apply substHeight in E0; solve_fs.
        eapply IHg with (n:=n1); solve_fs.
        rewrite E2. simpl. auto.
    ++  destruct_guard_in H3.
        destruct_guard_in H3; inv H3.
        econstructor; auto.
    +++ destruct (in_list_spec v0 (FV u)); auto. inv E.
    +++ eapply IHg with (n:= n); solve_fs.
        rewrite E0. simpl. auto.
Qed.

Lemma substTerm t x u :
    fst (subst' (height t) t x u (1+termListMaxVar [Var x; u; t])) <> None.
Proof.
    intros.
    pose proof (MaxVarsFresh (Var x) 0).
    set (n1 := max 0 (termMaxVar _)) in *.
    pose proof (MaxVarsFresh u n1).
    set (n2 := max n1 (termMaxVar u)) in *.
    pose proof (V1:= MaxVarsFresh t n2).
    set (n3 := max n2 (termMaxVar t)) in *.
    remember n3 as n. unfold n3, n2, n1 in *.
    clear n3 n2 n1.
    assert (V2: FreshState (S n) u). {
        eapply FreshStateLeq; [|apply H0].
        subst. apply le_n_S. lia.
    }
    assert (V3: FreshState (S n) (Var x)). {
        eapply FreshStateLeq; [|apply H].
        subst. lia.
    }
    clear H H0.
    apply substTermEx; auto.
Qed.

Definition subst t x u :=
    get_some
    (fst (subst' (height t) t x u (1+termListMaxVar [Var x; u; t])))
    (substTerm t x u).

Lemma substSpec:
    ∀ t x u, t⎡x → u⎤ ~ subst t x u.
Proof.
    unfold subst. intros.
    pose proof (MaxVarsFresh (Var x) 0).
    set (n1 := max 0 (termMaxVar _)) in *.
    pose proof (MaxVarsFresh u n1).
    set (n2 := max n1 (termMaxVar u)) in *.
    pose proof (V1:= MaxVarsFresh t n2).
    set (n3 := max n2 (termMaxVar t)) in *.
    remember n3 as n. unfold n3, n2, n1 in *.
    clear n3 n2 n1.
    assert (V2: FreshState (S n) u). {
        eapply FreshStateLeq; [|apply H0].
        subst. lia.
    }
    assert (V3: FreshState (S n) (Var x)). {
        eapply FreshStateLeq; [|apply H].
        subst. lia.
    }
    clear H H0.
    apply get_some_ind .
    destruct (fst (subst' (height t) t x u (S (termListMaxVar [Var x; u; t])))) eqn:E.
    +   exists l. split; auto. eapply SubstImpl; eauto.
        subst. cbn in E. cbn. apply E.
    +   exfalso. subst. eapply substTermEx in E; eauto.
Qed.

Fixpoint decVarAlpha xs ys x y : bool :=
    match xs, ys with
    | xs'::x', ys'::y' =>
        match x =v? x', y =v? y' with
        | true, true => true
        | false, false => decVarAlpha xs' ys' x y 
        | _, _ => false
        end
    | [], [] => x =v? y
    | _, _ => false
    end.

Fixpoint decAlpha xs ys x y :=
    match x, y with
    | Var x, Var y => decVarAlpha xs ys x y
    | App f1 t1, App f2 t2 => decAlpha xs ys f1 f2 && decAlpha xs ys t1 t2
    | Abs a t1, Abs b t2 => decAlpha (xs::a) (ys::b) t1 t2
    | _, _ => false
    end.

Lemma VarAlpha_spec: 
    ∀ xs ys x y , 
        decVarAlpha xs ys x y = true <-> VarAlpha xs ys x y.
Proof.
    induction xs; destruct ys; simpl; split; intros; try (inv H; fail).
    +   destruct (eqvb_reflect x y); subst; [constructor|inv H].   
    +   destruct (eqvb_reflect x y); subst; [constructor|inv H; contradiction].   
    +   destruct (eqvb_reflect x t); destruct (eqvb_reflect y v); subst; 
            try (inv H; fail); try constructor; auto.
        apply IHxs, H.
    +   destruct (eqvb_reflect x t); destruct (eqvb_reflect y v); subst; 
            try constructor; auto.
    ++  inv H; contradiction.
    ++  inv H; contradiction.
    ++  inv H; try contradiction.
        apply IHxs. auto.
Qed.


Lemma decAlphaSpec: 
    ∀ t u xs ys, 
        decAlpha xs ys t u = true <-> Alpha xs ys t u.
Proof.
    induction t; simpl; intros; split; intros.
    +   destruct u; try inv H.
        constructor. apply VarAlpha_spec, H1.   
    +   destruct u; try inv H.
        apply VarAlpha_spec, H4.   
    +   destruct u; try inv H.
        apply andb_true_iff in H1 as [H1 H2].
        constructor.
    ++  apply IHt1; auto.
    ++  apply IHt2; auto.
    +   destruct u; try inv H.
        apply andb_true_iff. split.
    ++  apply IHt1; auto.
    ++  apply IHt2; auto.
    +   destruct u; try inv H.
        constructor.
        apply IHt, H1.
    +   destruct u; try inv H.
        apply IHt, H3.
Qed.


Fixpoint bvcRefresh' (g:nat) (t:Lam) ts: M nat Lam :=
    match g with 
    | 0 => fail
    | S g => 
    match t with
    | Var x => ret (Var x)
    | App f u => 
        f' <- bvcRefresh' g f ts ;;
        u' <- bvcRefresh' g u ts ;;
        ret (App f' u')
    | Abs y u =>
        if in_list y ts then 
            y' <- fresh;;
            u' <- subst' g u y (Var y')  ;;
            u'' <-  bvcRefresh' g u' ts ;;
            ret (Abs y' u'')
        else
            u' <- bvcRefresh' g u ts;;
            ret (Abs y u')
    end
    end.


Lemma bvcRefreshIncreases: 
    ∀ g t xs n o n', 
    bvcRefresh' g t xs n = (o, n') ->
    n' >= n.
Proof.
    induction g; intros.
    +   cbn in H. inv H. lia.
    +   cbn in H. destruct t.
    ++  inv H. lia.
    ++  destruct (bvcRefresh' g t1 xs n) eqn:E1.
        destruct o0; [|inv H; apply IHg in E1; auto].
        destruct (bvcRefresh' g t2 xs n0) eqn:E2.
        destruct o0; inv H; apply IHg in E1, E2; lia.
    ++  destruct (in_list_spec v xs).
    +++ destruct (subst' g t v (Var (var n)) (S n)) eqn:E1.
        destruct o0; [|inv H; apply SubstIncreasesM in E1; lia].
        destruct (bvcRefresh' g l xs n0) eqn:E2.
        destruct o0; inv H; apply SubstIncreasesM in E1; apply IHg in E2; lia.
    +++ destruct (bvcRefresh' g t xs n) eqn:E1.
        destruct o0; inv H; apply IHg in E1; auto.
Qed.

Lemma bvcRefreshEnoughGas': 
    ∀ g g' t xs n , 
    g >= g' ->
    g' >= height t ->
    bvcRefresh' g' t xs n = bvcRefresh' (height t) t xs n.
Proof.
    induction g; intros. { pose proof (HeightNot0 t). lia. }
    destruct g'. { pose proof (HeightNot0 t). lia. }
    destruct t.
    +   cbn in *. auto.
    +   cbn in H0 |- *.
        rewrite IHg; try lia. 
        destruct (bvcRefresh' (height t1) t1 xs n) eqn:E1.
        rewrite (IHg _ t1); try lia. rewrite E1.
        destruct o; auto.
        rewrite IHg; try lia.
        destruct (bvcRefresh' (height t2) t2 xs n0) eqn:E2.
        rewrite (IHg _ t2); try lia. rewrite E2. 
        reflexivity.
    +   cbn in H0 |- *. 
        destruct (in_list_spec v xs).
    ++  rewrite substEnoughGas; auto; try lia.
        destruct (subst' (height t) t v (Var (var n)) (S n)) eqn:E2.
        destruct o; auto.
        apply substHeight in E2 as E3.
        rewrite IHg; try lia.
        rewrite E3.
        reflexivity.
    ++  rewrite IHg; try lia.
        reflexivity.
Qed.

Lemma bvcRefreshEnoughGas: 
    ∀ g t xs n , 
    g >= height t ->
    bvcRefresh' g t xs n = bvcRefresh' (height t) t xs n.
Proof.
    intros. eapply (bvcRefreshEnoughGas' g g); auto.
Qed.


Lemma bvcRefreshAlpha': 
    ∀ g t xs n t', 
    g >= height t ->
    FreshState n t ->
    (* Forall (fun v => FreshState n (Var v)) xs -> *)
    fst (bvcRefresh' g t xs n) = Some t' ->
    Alpha [] [] t t'.
Proof.
    induction g; intros. { pose proof (HeightNot0 t). lia. }
    destruct t.
    +   cbn in H1. inv H1. apply AlphaRefl.
    +   cbn in H, H1.
        rewrite bvcRefreshEnoughGas in H1; [|lia].
        destruct (bvcRefresh' (height t1) t1 xs n) eqn:E1.
        destruct o; [|inv H1].
        rewrite bvcRefreshEnoughGas in H1; [|lia].
        destruct (bvcRefresh' (height t2) t2 xs n0) eqn:E2.
        destruct o; [|inv H1].
        apply FreshStateApp in H0 as [H3 H4].
        inv H1. constructor.
    ++  eapply IHg; eauto; try lia.
        rewrite bvcRefreshEnoughGas; try lia. rewrite E1. auto.
    ++  apply bvcRefreshIncreases in E1 as F3.
        assert (FreshState n0 t2). { eapply FreshStateLeq; [|eauto]. auto. } clear H4.
        (* assert (Forall (fun v : V => FreshState n0 (Var v)) xs). {
            clear -H1 F3. induction xs; [constructor|]. inv H1. 
            constructor; auto.  eapply FreshStateLeq; eauto.  
        } clear H1. *)
        eapply IHg; eauto; try lia. 
        rewrite bvcRefreshEnoughGas; try lia. rewrite E2. auto.
    +   cbn in H, H1. destruct (in_list_spec v xs).
    ++  rewrite substEnoughGas in H1; try lia.
        destruct (subst' (height t) t v (Var (var n)) (S n)) eqn:E2.
        destruct o; [|inv H1].
        apply substHeight in E2 as E5.
        rewrite bvcRefreshEnoughGas in H1; try lia.
        destruct (bvcRefresh' (height l) l xs n0) eqn:E3.
        destruct o; [|inv H1].
        inv H1.
        apply FreshStateAbs in H0 as [H2 H3].
        apply SubstIncreasesM in E2 as F3.
        assert (FreshState n0 t). { eapply FreshStateLeq; [|eauto]. lia. }
        (* assert (Forall (fun v : V => FreshState n0 (Var v)) xs). {
            clear -H1 F3. induction xs; [constructor|]. inv H1. 
            constructor; auto. eapply FreshStateLeq; [|eauto]. lia.  
        } clear H1. *)
        assert (W1:fst (subst' (height t) t v (Var (var n)) (S n)) = Some l) . {
            rewrite E2. auto.
        }
        assert (FreshState (S n) (Var v)). {
            intros v0 P [L|[]]. subst. eapply (H2 v0); auto. lia.
        }
        assert (FreshState (S n) t). { eapply FreshStateLeq; [|apply H3]. lia. } 
        assert (FreshState (S n) (Var (var n))). { 
            intros v0 P [L|[]].  apply var_inj in L. subst. lia.
        }
        eapply SubstImpl in W1; auto.
        eapply AlphaTrans. {
            apply SubstFreshVarAlpha; eauto.
        }
        apply AlphaConvAbs. 
        
        assert (FreshState n0 l). { 
            eapply substFreshState in E2; auto.
        }
        eapply IHg; eauto; [lia|].
        rewrite bvcRefreshEnoughGas; [|lia].
        rewrite E3. auto.
    ++  destruct (bvcRefresh' g t xs n) eqn:E2.
        destruct o; [|inv H1].
        inv H1.
        apply AlphaConvAbs.
        apply FreshStateAbs in H0 as [H2 H3].
        eapply IHg; eauto; [lia|].
        rewrite E2. auto. 
Qed.

Fixpoint ssubst (t:Lam) (x:V) (u:Lam) : Lam :=
    match t with 
    | Var v   => if v =v? x then u else Var v
    | App f v => App (ssubst f x u) (ssubst v x u) 
    | Abs y v => if y =v? x then Abs y v else Abs y (ssubst v x u)
    end.


Theorem bvcRefreshTermEx g : ∀ t xs st,
    FreshState st t ->
    (* Forall (fun v => FreshState st (Var v)) xs -> *)
    g >= height t ->
    fst (bvcRefresh' g t xs st) <> None.
Proof.
    induction g; intros t xs st Hft Hg. { pose proof (HeightNot0 t). lia. }
    destruct t.
    +   cbn. intro C. inv C.
    +   cbn in Hg |- *.
        apply FreshStateApp in Hft as [Hft1 Hft2].
        destruct_guard.
        destruct o.
    ++  destruct_guard.
        destruct o.
    +++ intro C. inv C. 
    +++ assert (FreshState n t2). { apply bvcRefreshIncreases in E. eapply FreshStateLeq; [|eauto]. lia.  }
        (* assert (Forall (fun v : V => FreshState n (Var v)) xs). { 
            clear -Hfxs E. apply bvcRefreshIncreases in E.
            induction xs; [constructor|]. inv Hfxs. constructor; auto. 
            eapply FreshStateLeq; [|eauto]. lia.  
        } *)
        epose proof (IHg _ _ _ H  ).
        rewrite E0 in H0. apply H0. lia.
    ++  epose proof (IHg _ _ _ Hft2 ).
        rewrite E in H. apply H. lia.
    +   cbn in Hg |- *.
        apply FreshStateAbs in Hft as [Hft1 Hft2].
        destruct_guard.
    ++  destruct_guard.
        epose proof (substTermEx _ _ _ _ _ ).
        rewrite E0 in H.
        destruct o.
    +++ destruct_guard.
        assert (FreshState n l). { 
            apply substFreshState  in E0 as W; auto.
            *   apply SubstIncreasesM in E0.
                eapply FreshStateLeq; [|eauto]. lia.
            *   intros v0 C P. inv P; [|inv H0]. 
                apply var_inj in H0. subst. lia.
        }
        (* assert (Forall (fun v : V => FreshState n (Var v)) xs). { 
            clear -Hfxs E0. apply SubstIncreasesM in E0.
            induction xs; [constructor|]. inv Hfxs. constructor; auto. 
            eapply FreshStateLeq; [|eauto]. lia.  
        } *)
        epose proof (IHg _ _ _ H0 ).
        destruct o.
        *   intro C. inv C.
        *   rewrite E1 in H1. apply H1. 
            apply substHeight in E0.
            lia.
    +++ apply H. lia.
    ++  destruct_guard. destruct o.
    +++ cbn. intro C. inv C.
    +++ epose proof (IHg _ _ _ Hft2).
        rewrite E0 in H. apply H. lia.
Qed.


Lemma FreshStateMaxVar:
    ∀ f a t,
    FreshState (S a) t  -> FreshState (S (max a f)) t.
Proof.
    intros a b t H n Hn.
    apply H. lia.
Qed.

Lemma bvcRefreshTerm: ∀ t xs,
  let r := bvcRefresh' (height t) t xs (1 + max (varListMaxVar xs) (termMaxVar t)) 
  in fst r <> None.
Proof.
    intros.
    apply bvcRefreshTermEx; auto.
    simpl. apply MaxVarsFresh.
Qed.

Lemma eq_to_fst:
    ∀ {A B} (t:A*B) x y,
    t = (x, y) -> fst t = x.
Proof. intros. rewrite H. auto. Qed.


Definition bvcRefresh t xs :=
  let r := bvcRefresh' (height t) t xs (1 + max (varListMaxVar xs) (termMaxVar t)) 
  in get_some (fst r) (bvcRefreshTerm t xs).

Theorem bvcRefreshAlpha: 
    ∀ t vs, t =α (bvcRefresh t vs) .
Proof.
    unfold bvcRefresh. intros. 
    apply get_some_ind .
    destruct (bvcRefresh' (height t) t vs  (1 + max (varListMaxVar vs) (termMaxVar t)) ) eqn:E.
    destruct o.
    +   exists l. split; auto.
        eapply eq_to_fst, bvcRefreshAlpha' in E; auto.
    ++  simpl. apply MaxVarsFresh.
    +   exfalso. eapply bvcRefreshTerm. rewrite E. auto.
Qed.


Corollary subst_var_not_FV:
    ∀ t v x,
    ~ In x (FV t) ->
    subst t x v =α t.
Proof.
    intros. apply AlphaSym.
    pose proof (substSpec t x v).
    apply AlphaSubstUnusedVar in H0; auto.
Qed.

Lemma subst_change_term:
    ∀ t t' x v,
    t =α t' ->
    subst t x v =α subst t' x v.
Proof.
    intros. 
    pose proof (substSpec t x v).
    pose proof (substSpec t' x v).
    eapply (SubstAlpha t t' v v); eauto; try apply AlphaRefl. 
    constructor.
    apply AlphaCtxImplGlobs with (xs:=[]) (ys:=[])(zs:=[x]); auto.
Qed.

Lemma subst_change_subst:
    ∀ t x v v',
    v =α v' ->
    subst t x v =α subst t x v'.
Proof.
    intros. 
    pose proof (substSpec t x v).
    pose proof (substSpec t x v').
    eapply (SubstAlpha t t v v'); eauto; try apply AlphaRefl.
Qed.


Inductive BVC xs: Lam -> Prop :=
    | BVCVar v: BVC xs (Var v)
    | BVCApp f t: BVC xs f -> BVC xs t -> BVC xs (App f t)
    | BVCAbs v t: ~In v xs -> BVC xs t -> BVC xs (Abs v t)
    .

Lemma bvcRefresh'_prop:
    ∀ g t t' xs n,
    g >= height t ->
    FreshState n t ->
    Forall (fun v => FreshState n (Var v)) xs ->
    fst (bvcRefresh' g t xs n) = Some t' ->
    BVC xs t'.
Proof.
    induction g; intros t t' xs n Hg Hf Hxs H. {
        pose proof (HeightNot0 t). lia.
    }
    destruct t; simpl in Hg.
    +   cbn in *. inv H. constructor.
    +   cbn in *.
        apply FreshStateApp in Hf as [Hf1 Hf2].
        destruct_guard_in H.
        destruct o; [|inv H].
        destruct_guard_in H. 
        destruct o; [|inv H].
        inv H. constructor.
    ++  eapply (IHg t1); eauto; [lia|].
        rewrite E. auto.
    ++  apply bvcRefreshIncreases in E as F1.
        assert (FreshState n0 t2). { eapply FreshStateLeq; [|eauto]. auto. } clear Hf2.
        assert (Forall (fun v : V => FreshState n0 (Var v)) xs). {
            clear -Hxs F1. induction xs; auto; [constructor|]. inv Hxs. 
            constructor; auto. eapply FreshStateLeq; eauto.  
        } clear Hxs.
        eapply (IHg t2); eauto; [lia|].
        rewrite E0. auto.
    +   apply FreshStateAbs in Hf as [Hf1 Hf2].
        cbn in H. destruct (in_list_spec v xs).
    ++  destruct_guard_in H.
        destruct o; [|inv H].
        destruct_guard_in H.
        destruct o; [|inv H].
        cbn in H. inv H. 
        constructor.
    +++ clear -i Hxs Hf1. induction xs ;auto.
        intros [C|C].
        *   subst. inv Hxs. apply IHxs; auto.
        **  inv i; auto.
            exfalso. apply (Hf1 n); auto.
        **  exfalso. eapply H1 with (v:=n); cbn; auto.
        *   inv Hxs.  inv i.
        **  rewrite Forall_forall in H2.
            apply H2 in C. eapply C with (v:=n); auto.
            cbn. tauto.
        **  eapply IHxs; eauto. 
    +++ apply SubstIncreasesM in E as F1.
        assert (FreshState (S n) t). { eapply FreshStateLeq; [|eauto]. auto. } clear Hf2.
        assert (FreshState (S n) (Var (var n))). { 
            intros v0 H1 [C|[]]. apply var_inj in C. inv C. lia.
        }
        apply substFreshState in E as F2; eauto.
        assert (Forall (fun v : V => FreshState n0 (Var v)) xs). {
            clear -Hxs F1. induction xs; auto; [constructor|]. inv Hxs. 
            constructor; auto. eapply FreshStateLeq; [|eauto]. lia.  
        } clear Hxs.
        eapply (substHeight) in E.
        eapply IHg; eauto; [lia|].
        rewrite E0. auto.
    ++  destruct_guard_in H.
        destruct o; [|inv H].
        cbn in H. inv H.
        constructor; eauto.
        eapply IHg; eauto; [lia|].
        rewrite E. auto. 
Qed.


Lemma InListFreshState:
    ∀ xs x,
    x ∈ xs -> FreshState (S (varListMaxVar xs)) (Var x).
Proof.
    induction xs; intros; inv H.
    +   cbn. unfold varToOrZero. destruct_guard.
    ++  intros v Q R. inv R; [|inv H]. 
        apply to_nat_var, var_inj in E. subst. lia. 
    ++  intros v Q R. inv R; [|inv H]. 
        eapply to_nat_none with (n:=v) in E. apply E. auto.
    +   cbn. apply IHxs in H0. clear IHxs.
        unfold varToOrZero. destruct_guard;[|apply FreshStateMaxVar]; auto.
        intros v Q R. inv R; [|inv H].
        eapply H0 with (v:=v); try lia.
        left. auto.
Qed.

Lemma bvcRefreshProp:
    ∀ t vs,
    BVC vs (bvcRefresh t vs).
Proof.
    intros. unfold bvcRefresh.
    apply get_some_ind .
    destruct (bvcRefresh' (height t) t (vs)  (1 + max (varListMaxVar vs) (termMaxVar t))) eqn:E.
    destruct o.
    +   exists l. split; auto. 
        apply eq_to_fst in E.
        eapply bvcRefresh'_prop in E; eauto.
    ++  apply MaxVarsFresh.
    ++  rewrite Forall_forall.
        intros x H. simpl. apply FreshStateMaxVar.
        apply InListFreshState, H.
    +   exfalso. eapply bvcRefreshTermEx; [| | rewrite E]; auto.
        apply MaxVarsFresh. 
Qed.

Lemma BVCssubst:
    ∀ t x xs v,
    BVC xs v ->
    BVC xs t -> 
    BVC xs (ssubst t x v).
Proof.
    intros t x xs v Hv Ht. induction Ht; cbn.
    +   destruct (eqvb_reflect v0 x); auto.
        constructor.
    +   constructor; auto.
    +   destruct_guard; constructor;auto.
Qed.


Lemma BVCprop:
    ∀ t x v xs,
    x ∈ xs ->
    Forall (fun v => v ∈ xs) (FV v) ->
    BVC xs t ->
    t ⎡ x → v ⎤ ~ ssubst t x v.
Proof.
    intros t x v xs Hx Hfv H.
    induction H.
    +   cbn. destruct (eqvb_reflect v0 x).
    ++  subst. constructor.
    ++  constructor; auto.
    +   cbn. constructor; auto.
    +   cbn. destruct (eqvb_reflect v0 x).
    ++  subst. contradiction.
    ++  constructor; auto.
        rewrite Forall_forall in Hfv.
        intro C. apply Hfv in C. contradiction.
Qed.

Property ssubst_BVC:
    ∀ t x v,
    BVC (FV (v)::x) t ->
    t ⎡ x → v ⎤ ~ ssubst t x v.
Proof.
    intros. eapply BVCprop in H; eauto.
    + cbn. tauto.
    +   apply Forall_forall. intros. cbn. tauto.
Qed.

Lemma bvcEq:
    ∀ t x xs v,
    x ∈ xs ->
    FV v ⊆ xs ->
    BVC xs t ->
    subst t x v =α ssubst t x v.
Proof.
    intros. 
    pose proof (substSpec t x v).
    pose proof (BVCprop t x v).
    eapply SubstAlpha_Simple; eauto.
Qed.


Lemma ssubst_not_in:
    ∀ t x v,
    x ∉ FV t -> ssubst t x v = t.
Proof.
    induction t; cbn; intros; auto.
    +   apply not_or_iff in H as [H _].
        apply eqvb_neq in H. rewrite H. auto.
    +   rewrite in_app_iff in H.
        apply not_or_iff in H as [H1 H2].
        rewrite (IHt1 _ _ H2).
        rewrite (IHt2 _ _ H1).
        auto.
    +   rewrite filter_In in H.
        destruct (eqvb_reflect v x); auto.
        f_equal. apply IHt. tauto.
Qed.

Lemma ssubst_swap:
    ∀ t  x y u1 u2 ,
    x <> y ->
    BVC [y] t ->
    x ∉ FV u2 ->
    ssubst (ssubst t x u1) y u2 = ssubst (ssubst t y u2) x (ssubst u1 y u2).
Proof.
    induction t; cbn; intros x y u1 u2 H A H0.
    +   destruct (eqvb_reflect v x).
    ++  subst. apply eqvb_neq in H. rewrite H. cbn.
        rewrite eqvb_refl. auto.
    ++  cbn. destruct_guard; [rewrite ssubst_not_in; auto|].
        cbn. apply eqvb_neq in n. rewrite n. auto.
    +   inv A.
        rewrite IHt1; auto. rewrite IHt2; auto.
    +   destruct (eqvb_reflect v x), (eqvb_reflect v y).
    ++  subst. contradiction.
    ++  subst. cbn.
        rewrite eqvb_refl.
        apply eqvb_neq in H. rewrite H. auto.
    ++  subst. inv A. cbn in H3. tauto.
    ++  cbn. inv A.
        apply eqvb_neq in n. rewrite n. auto.
        apply eqvb_neq in n0. rewrite n0.
        rewrite IHt; auto.
Qed.


Lemma  InFVssubst:
    ∀ t x u y,
    y ∈ FV (ssubst t x u) -> y ∈ (FV t) \/ y ∈ (FV u).
Proof.
    induction t; cbn; intros.
    +   destruct (eqvb_reflect v x).
    ++  subst. tauto.
    ++  cbn in H. destruct H as [H|[]]. subst. tauto.
    +   rewrite in_app_iff in H. destruct H.
    ++  apply IHt2 in H. rewrite in_app_iff. tauto.
    ++  apply IHt1 in H. rewrite in_app_iff. tauto.
    +   destruct (eqvb_reflect v x).
    ++  cbn in H. rewrite filter_In in H. destruct H. 
        subst. rewrite filter_In. tauto.
    ++  cbn in H. rewrite filter_In in *.
        destruct H. apply IHt in H. tauto.
Qed.

Lemma BVCmiddle:
    ∀ t xs ys zs ,
        BVC ((zs++ys)++xs) t -> BVC ys t.
Proof.
    induction t; intros.
    +   constructor.
    +   inv H. constructor.
    ++  eapply IHt1; eauto.
    ++  eapply IHt2; eauto.
    +   inv H. 
        do 2 rewrite in_app_iff in H2.
        do 2 rewrite not_or_iff in H2.
        destruct H2, H0.
        induction xs; cbn in *.
    ++  constructor; auto. eapply (IHt []); eauto.
    ++  rewrite not_or_iff in H. destruct H.
        constructor; auto. eapply (IHt (xs::t0) ys zs ); eauto.
Qed.

Lemma Subset_app: 
    ∀ {A} (xs ys zs: slist A), (xs ⊆ ys \/ xs ⊆ zs) -> xs ⊆ (ys ++ zs).
Proof.
    intros A. induction xs; intros; constructor; destruct H; inv H.
    +   apply in_app_iff. tauto.
    +   apply in_app_iff. tauto.
    +   apply IHxs. auto.
    +   apply IHxs. auto.
Qed.


Theorem SubstSwap:
    ∀ t1 t2 t3 u1 u2 x y u1' t2' t3',
    x ≠ y -> x ∉ FV u2 ->
    t1⎡ x → u1 ⎤ ~ t2 -> t2⎡ y → u2 ⎤ ~ t3 ->
    u1⎡ y → u2 ⎤ ~ u1' ->
    t1⎡ y → u2 ⎤ ~ t2' -> t2'⎡ x → u1' ⎤ ~ t3' ->
    t3 =α t3'.
Proof.
    intros t1 t2 t3 u1 u2 x y u1' t2' t3' H H1 H2 H3 B1 A1 A2.
    
    pose proof (A3:=substSpec t2' x u1').
    eapply AlphaTrans;
    [|eapply SubstAlpha_Simple; eauto; apply AlphaRefl].

    pose proof (A4:=substSpec t1 y u2).

    eapply AlphaTrans;
    [|eapply subst_change_term, AlphaSym, SubstAlpha_Simple ; eauto; apply AlphaRefl].

    pose proof (A5:=substSpec u1 y u2).
    eapply AlphaTrans;
    [|eapply subst_change_subst, SubstAlpha_Simple; eauto; apply AlphaRefl].

    pose proof (A6:=substSpec t2 y u2).
    eapply AlphaTrans;
    [eapply SubstAlpha_Simple; eauto; apply AlphaRefl|].

    pose proof (A7:=substSpec t1 x u1).
    eapply AlphaTrans;
    [apply subst_change_term; eapply SubstAlpha_Simple; eauto; apply AlphaRefl|].

    clear -H H1.

    pose proof (bvcRefreshAlpha t1 (FV u2 ++ FV u1 ++ [y; x])).
    set (t1':= bvcRefresh t1 _ ) in *.

    eapply AlphaTrans;
    [eapply subst_change_term; eapply subst_change_term, H0|].

    eapply AlphaTrans;
    [|eapply subst_change_term, subst_change_term, AlphaSym, H0].
    
    pose proof (bvcRefreshAlpha u1 (FV u2 ++ FV u1 ++ [y; x])).
    set (u1':= bvcRefresh u1 _ ) in *.

    eapply AlphaTrans;
    [eapply subst_change_term, subst_change_subst, H2|].
    
    eapply AlphaTrans;
    [|eapply subst_change_subst, subst_change_term, AlphaSym, H2].

    pose proof (bvcRefreshAlpha u2 (FV u2 ++ FV u1 ++ [y; x])).
    set (u2':= bvcRefresh u2 _ ) in *.

    eapply AlphaTrans;
    [eapply subst_change_subst, H3|].

    eapply AlphaTrans;
    [|eapply subst_change_term, subst_change_subst, AlphaSym, H3].

    eapply AlphaTrans;
    [|eapply subst_change_subst, subst_change_subst, AlphaSym, H3].

    erewrite AlphaFV in H1; eauto.

    assert (x ∈ (FV u2 ++ FV u1 ++ [y; x])). {
        cbn. tauto.
    } 
    assert (y ∈ (FV u2 ++ FV u1 ++ [y; x])). {
        repeat (cbn; rewrite in_app_iff). tauto.
    } 

    assert (Forall (λ v : V, v ∈ (FV u2 ++ FV u1 ++ [y; x])) (FV u1')). {
        apply Subset_app. right.
        erewrite AlphaFV; [|apply H2].
        apply Subset_app. left.
        apply Forall_forall. auto.
    }

    assert (Forall (λ v : V, v ∈ (FV u2 ++ FV u1 ++ [y; x])) (FV u2')). {
        apply Subset_app. left.
        erewrite AlphaFV; [|apply H3].
        apply Forall_forall. auto.
    }

    eapply AlphaTrans;
    [eapply subst_change_term, bvcEq; [apply H4| apply H6 | apply bvcRefreshProp ]|].

    eapply AlphaTrans;
    [|eapply subst_change_term, AlphaSym, bvcEq; [apply H5| apply H7 | apply bvcRefreshProp ]].    

    eapply AlphaTrans;
    [|eapply subst_change_subst, AlphaSym, bvcEq; [apply H5| apply H7 | apply bvcRefreshProp ]].    

    eapply AlphaTrans;
    [eapply bvcEq;[apply H5| apply H7 | apply BVCssubst; apply bvcRefreshProp ]|].

    assert (BVC ((FV u2 ++ FV u1 ++ [y; x])) (ssubst t1' y u2')). {
        apply BVCssubst; apply bvcRefreshProp.
    }
    assert (Forall (λ v : V, v ∈ (FV u2 ++ FV u1 ++ [y; x])) (FV (ssubst u1' y u2'))). {
        apply Forall_forall. intros. repeat (cbn; rewrite in_app_iff).
        eapply InFVssubst in H9.
        erewrite (AlphaFV u1') in H9; [|apply AlphaSym, H2].
        erewrite (AlphaFV u2') in H9; [|apply AlphaSym, H3].
        destruct H9; tauto.
    }
    eapply AlphaTrans;
    [|eapply AlphaSym, bvcEq; [apply H4| apply H9 |apply H8 ]].

    rewrite ssubst_swap; auto; [eapply AlphaRefl|].

    eapply (BVCmiddle _ [x] [y] (FV u2 ++ FV u1)). 

    apply (bvcRefreshProp t1 (FV u2 ++ FV u1 ++ [y; x])) .
Qed.



End Lam.

(* 
    Setup for testing: 
    Varialbles are either strings or nat-s; constants are nats.  
*)
From Stdlib Require Import String.
Module TestConf <: LamConf.

    Inductive Vt := | Sv: string -> Vt | Iv: nat -> Vt .
    Definition V := Vt.
    
    Definition eqvb x y := 
        match x, y with 
        | Sv x, Sv y => eqb x y  
        | Iv x, Iv y => Nat.eqb x y
        | _, _ => false
        end.
    

    Definition eqvb_reflect x y : reflect (x = y) (eqvb x y) .
    Proof.
        destruct x, y; cbn.
        +   destruct (eqb_spec s s0); subst; constructor; auto.
            intro C. inv C. contradiction.
        +   constructor. intro C. inv C.
        +   constructor. intro C. inv C.
        +   destruct (Nat.eqb_spec n n0); subst; constructor; auto.
            intro C. inv C. contradiction.
    Qed.

    Fixpoint in_list x xs : bool :=
        match xs with
        | [] => false
        | ys::y => if eqvb x y then true else in_list x ys 
        end.
    
    Lemma in_list_spec: ∀ x xs, reflect (In x xs) (in_list x xs).
    Proof.
        intros x. induction xs.
        +   constructor. intro C. inv C.
        +   cbn. destruct (eqvb_reflect x t).
        ++  constructor. left. auto.  
        ++  inv IHxs; constructor; try tauto.
            intro C. destruct C; subst; try contradiction.
    Qed.

    
    Definition var := Iv.
    Definition var_inj : ∀ x y, var x = var y <-> x=y.
    Proof. 
        intros. split; intros.
        +   inv H. auto.
        +   subst. auto.
    Defined.

    
    Definition to_nat v:=
        match v with Sv _ => None | Iv i => Some i end.

    Definition to_nat_var: ∀ v n, to_nat v = Some n -> v = var n.
    Proof.
        intros. destruct v; inv H. auto.
    Defined.

    Definition to_nat_none: ∀ v, to_nat v = None -> ∀ n, v <> var n. 
    Proof.
        intros. destruct v; inv H. intro C. inv C. 
    Defined.
End TestConf.

Module LamTest.
    Module L := Lam (TestConf).
    Import TestConf.
    Import L.

    (* 
        Setup to use notations for lambda-terms
    *)
    Notation string := (TestConf.V) .
    Definition to_string (s:list Byte.byte) := TestConf.Sv (string_of_list_byte s) .


    Definition from_string s := 
        match s with
        |   TestConf.Sv n => Some (list_byte_of_string n)
        |   _ => None
        end.

    Declare Scope lam_scope.
    Open Scope lam_scope.
    Unset Printing Coercions.

    String Notation TestConf.Vt to_string from_string : lam_scope.
    
    Definition V_in_Lam (b:TestConf.Vt) := Var b.
    Coercion V_in_Lam : TestConf.Vt >-> Lam.

    Definition Lam_in_App (b:Lam) := fun y => App b y.
    Coercion Lam_in_App : Lam >-> Funclass.

    (* Notation for Rocq lambdas clashes with lambda-term notation. Safe to ignore here. *)
    Set Warnings "-notation-incompatible-prefix".

    Notation "'λ' x ';' .. ';' y '.' z" := (Abs x .. (Abs y z) .. ) (at level 40).

    (*
        Tests
    *)

    Definition t1 := λ "x"; "y". "y".

    Compute (decAlpha [] [] (λ "x"; "y". "y") ( λ "y"; "x". "x")).

    Lemma Ktest: (λ "x"; "y". "y") =α ( λ "y". (λ "x". "x")).
    Proof.
        apply decAlphaSpec. reflexivity.
    Qed.

    Example test1: ((λ "q". "z") "y") =α ((λ "w". "z") "y").
Proof. apply decAlphaSpec. reflexivity. Qed.

    Example test2: ~ (λ "z". "z") "y" =α (λ "q". "z") "y" .
    Proof. intro. apply decAlphaSpec in H. discriminate H. Qed.

    Definition t := λ "x"; "y". "z" "x".

    Compute (subst t "z" "x").
    Compute ( (bvcRefresh t ["z"; "x"]) ).

End LamTest.


