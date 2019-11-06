Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
end.

Compute (next_weekday friday).

Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
  | true
  | false.

Definition negb (b:bool) :bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) :bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) :bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb5: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb6: false || false || true = true.
Proof. simpl. reflexivity. Qed.


Definition nandb (b1:bool) (b2:bool) :bool := 
  match b1 with
  | true => negb(b2)
  | false => true
  end.


Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | true => b2 && b3
  | false => false
  end.
Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

(* https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html Types *)

Check true.

Check (negb true).

Check negb.

Check andb.

Inductive rgb : Type := 
  | red
  | green
  | blue.

Inductive color: Type := 
  | black
  | white
  | primary(p: rgb).

Definition monochrome (c: color): bool := 
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

Definition isRed (c: color): bool := 
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

Compute (isRed(primary red)).

Definition isReallyRed (c: color): bool :=
  match c with
  | primary red => true
  | _ => false
  end.

Compute (isReallyRed black).

(* Tuples *)

Inductive bit : Type :=
  | B0
  | B1.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).
  
Check (bits B1 B0 B1 B0).
 
Definition all_zero (nb: nybble): bool := 
  match nb with
  | (bits B0 B0 B0 B0) => true
  | _ => false
  end.

Compute (all_zero (bits B1 B0 B1 B0)).
Compute (all_zero (bits B0 B0 B0 B0)).

(* Modules *)

Module NatPlayground.

(* Numbers *)

Inductive nat : Type :=
  | O
  | S (n: nat).

Definition pred (n: nat): nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End NatPlayground.

Check (S (S (S (S O)))).

Definition minusTwo (n: nat): nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end .

Compute (minusTwo (S (S (S (S O))))).
Compute (minusTwo 4).

Check S.
Check pred.
Check minusTwo.

Check NatPlayground.pred.

Check (NatPlayground.S NatPlayground.O).
Check (S O).

Fixpoint evenB (n: nat): bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenB n'
  end.

Definition oddB (n : nat) : bool := negb (evenB n).

Example test_oddB1: oddB 1 = true.
Proof. simpl. reflexivity. Qed.

Example test_oddB2: oddB 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Compute (plus 3 2).

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m : nat) : nat :=
  match n, m with
  | O, _ => O
  | S _, O => n
  | S n', S m' => minus n' m'
  end.
  
Compute (minus 5 3).

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.
  
Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => S O
  | S n' => mult (S n') (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

