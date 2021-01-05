Require Import Strings.String.
Local Open Scope string_scope. 
Local Open Scope list_scope.
Scheme Equality for string.
Require Import Strings.String.
Require Import Strings.Ascii.
Require Import Coq.ZArith.BinInt.
From Equations Require Import Equations.
From Coq Require Import Logic.FunctionalExtensionality.
Module DefinitionMatrices.
Implicit Types m n x y : nat.

Inductive NatType :=
  | error_nat : NatType
  | num :  nat -> NatType.

Inductive IntType :=
  | error_int : IntType
  | nr : Z -> IntType.

Inductive BoolType :=
  | error_bool : BoolType
  | boolean : bool -> BoolType.

Coercion boolean: bool >-> BoolType.
Coercion nr : Z >-> IntType.
Coercion num : nat >-> NatType.
Notation "nat( N )" := (num N).
Notation "bool( B )" := (boolean B).
Notation "int( I )" := (nr I).

Inductive AExp :=
| avar: string -> AExp (* Var ~> string *)
| anum: NatType -> AExp
| aplus: AExp -> AExp -> AExp
| asub: AExp -> AExp -> AExp
| amul: AExp -> AExp -> AExp (* Multiplication *)
| adiv: AExp -> AExp -> AExp (* Division *)
| amod: AExp -> AExp -> AExp. (* Modulo *)

(* Coercions for numerical constants and variables *)
Coercion anum: NatType >-> AExp.
Coercion avar: string >-> AExp. (* Var ~> string *)

(* Notations used for arithmetic operations *)
Notation "A +' B" := (aplus A B)(at level 50, left associativity).
Notation "A -' B" := (asub A B)(at level 50, left associativity).
Notation "A *' B" := (amul A B)(at level 48, left associativity).
Notation "A /' B" := (adiv A B)(at level 48, left associativity).
Notation "A %' B" := (amod A B)(at level 45, left associativity).

Inductive BExp :=
| berror
| btrue
| bfalse
| bvar: string -> BExp (* Variables of type bool *)
| blt : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp.

Notation "A <' B" := (blt A B) (at level 70).
Notation "!' A" := (bnot A)(at level 51, left associativity).
Notation "A &&' B" := (band A B)(at level 52, left associativity).
Notation "A ||' B" := (bor A B)(at level 53, left associativity).

Inductive Stmt :=
  | nat_decl: string -> AExp -> Stmt (* Declaration Stmt for variables of type nat *)
  | bool_decl: string -> BExp -> Stmt (* Declaration Stmt for variables of type bool *)
  | nat_assign : string -> AExp -> Stmt (* Assignment Stmt for variables of type nat *)
  | bool_assign : string -> BExp -> Stmt (* Assignment Stmt for variables of type nat *)
  | sequence : Stmt -> Stmt -> Stmt
  | while : BExp -> Stmt -> Stmt
  | ifthenelse : BExp -> Stmt -> Stmt -> Stmt
  | ifthen : BExp -> Stmt -> Stmt.

Notation "X :n= A" := (nat_assign X A)(at level 90).
Notation "X :b= A" := (bool_assign X A)(at level 90).
Notation "'iNat' X ::= A" := (nat_decl X A)(at level 90).
Notation "'iBool' X ::= A" := (bool_decl X A)(at level 90).
Notation "S1 ;;; S2" := (sequence S1 S2) (at level 93, right associativity).
Notation "'fors' ( A ~ B ~ C ) { S }" := (A ;;; while B ( S ;;; C )) (at level 97).






Inductive vec ( A : Type ) : nat-> Type :=
| nil : vec A 0
| cons : A -> forall n , vec A n -> vec A (S n).

Check vec.
Check nil.
Check cons.
Check (cons nat 1 0 (nil nat )). 
Check (cons nat 4 2 (cons nat 4 1 (cons nat 4 0 (nil nat)))).

Notation "x ;; v" := (cons x v) (at level 59).
Notation "[ ]" := nil.
Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) .. )).

(* matrice *)
(*Definition sorted'' (al : list nat) := forall i j,
    i < j < length al ->
    nth i al 0 <= nth j al 0.

Check nth : forall A : Type, nat -> list A -> A -> A.
Check nth_error : forall A : Type, list A -> nat -> option A.*)
Delimit Scope list_scope with list.
(*
Infix "::" := cons (at level 60, right associativity) : list_scope.
(* Lemma leb_le n m : (n <=? m) = true <-> n <= m. *)
Notation "[ ]" := nil (format "[ ]") : list_scope.

Inductive sorted : list nat -> Prop :=
| sorted_nil :
    sorted []
| sorted_1 : forall x,
    sorted [x]
| sorted_cons : forall x y l,
    x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Fixpoint insert (i : nat) (l : list nat) :=
  match l with
  | [] -> [i]
  | h :: t -> if i <=? h then i :: h :: t else h :: insert i t
  end.
Fixpoint sort (l : list nat) : list nat :=
  match l with
  | [] -> []
  | h :: t ⇒ insert h (sort t)
  end.
Example sort_pi :
  sort [3;1;4;1;5;9;2;6;5;3;5]
  = [1;1;2;3;3;4;5;5;5;6;9].
Proof. simpl. reflexivity. Qed.
*)
(* mergesort *)
(*
 Fixpoint merge l1 l2 {struct l1} :=
  let fix merge_aux l2 :=
  match l1, l2 with
  | [], _ -> l2
  | _, [] -> l1
  | a1::l1', a2::l2' ->
      if a1 <=? a2 then a1 :: merge l1' l2 else a2 :: merge_aux l2'
  end
  in merge_aux l2. *)


(* rewrite la swap *)