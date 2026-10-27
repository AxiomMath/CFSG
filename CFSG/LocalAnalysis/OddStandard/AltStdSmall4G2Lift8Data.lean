module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.OddStandard.AltStdSmall4.G2

open Matrix

@[expose] def X8 : Matrix (Fin 3) (Fin 3) (ZMod 8) := !![0, 0, 5; 4, 7, 4; 5, 0, 0]

@[expose] def Y8 : Matrix (Fin 3) (Fin 3) (ZMod 8) := !![0, 1, 2; 1, 2, 1; 1, 1, 6]

@[expose] def fourM (m : Fin 3 → Fin 3 → Bool) : Matrix (Fin 3) (Fin 3) (ZMod 8) :=
  Matrix.of fun i j => if m i j then 4 else 0

@[expose] def GenRel8 (X Y : Matrix (Fin 3) (Fin 3) (ZMod 8)) : Prop :=
  X * X = 1 ∧ Y * Y * Y = 1 ∧ (X * Y) ^ 7 = 1 ∧ (X * Y * X * (Y * Y)) ^ 4 = 1

namespace Lift8

@[ext] structure Mat3 where
  e00 : ZMod 8
  e01 : ZMod 8
  e02 : ZMod 8
  e10 : ZMod 8
  e11 : ZMod 8
  e12 : ZMod 8
  e20 : ZMod 8
  e21 : ZMod 8
  e22 : ZMod 8

@[expose] def ofMatrix (M : Matrix (Fin 3) (Fin 3) (ZMod 8)) : Mat3 :=
  ⟨M 0 0, M 0 1, M 0 2, M 1 0, M 1 1, M 1 2, M 2 0, M 2 1, M 2 2⟩

@[expose] def toMatrix (A : Mat3) : Matrix (Fin 3) (Fin 3) (ZMod 8) :=
  !![A.e00, A.e01, A.e02; A.e10, A.e11, A.e12; A.e20, A.e21, A.e22]

@[expose] def mul (A B : Mat3) : Mat3 :=
  ⟨A.e00 * B.e00 + A.e01 * B.e10 + A.e02 * B.e20, A.e00 * B.e01 + A.e01 * B.e11 + A.e02 * B.e21,
    A.e00 * B.e02 + A.e01 * B.e12 + A.e02 * B.e22, A.e10 * B.e00 + A.e11 * B.e10 + A.e12 * B.e20,
    A.e10 * B.e01 + A.e11 * B.e11 + A.e12 * B.e21, A.e10 * B.e02 + A.e11 * B.e12 + A.e12 * B.e22,
    A.e20 * B.e00 + A.e21 * B.e10 + A.e22 * B.e20, A.e20 * B.e01 + A.e21 * B.e11 + A.e22 * B.e21,
    A.e20 * B.e02 + A.e21 * B.e12 + A.e22 * B.e22⟩

@[expose] def one : Mat3 := ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩

@[expose] def pow (A : Mat3) : ℕ → Mat3
  | 0 => one
  | n + 1 => mul (pow A n) A

theorem toMatrix_ofMatrix (M : Matrix (Fin 3) (Fin 3) (ZMod 8)) : toMatrix (ofMatrix M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem toMatrix_injective : Function.Injective toMatrix := by
  intro A B h
  have e : ∀ i j : Fin 3, toMatrix A i j = toMatrix B i j := fun i j => by rw [h]
  ext
  exacts [e 0 0, e 0 1, e 0 2, e 1 0, e 1 1, e 1 2, e 2 0, e 2 1, e 2 2]

theorem toMatrix_mul (A B : Mat3) : toMatrix (mul A B) = toMatrix A * toMatrix B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, mul, Matrix.mul_apply, Fin.sum_univ_three]

theorem toMatrix_one : toMatrix one = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem toMatrix_pow (A : Mat3) (n : ℕ) : toMatrix (pow A n) = toMatrix A ^ n := by
  induction n with
  | zero => exact toMatrix_one
  | succ n ih => rw [pow, toMatrix_mul, ih, pow_succ]

@[expose] def isOne (A : Mat3) : Bool :=
  A.e00 == 1 && A.e01 == 0 && A.e02 == 0 && A.e10 == 0 && A.e11 == 1 && A.e12 == 0 &&
    A.e20 == 0 && A.e21 == 0 && A.e22 == 1

theorem isOne_iff (A : Mat3) : isOne A = true ↔ toMatrix A = 1 := by
  rw [← toMatrix_one, toMatrix_injective.eq_iff]
  cases A
  simp only [isOne, one, Bool.and_eq_true, beq_iff_eq, Mat3.mk.injEq, and_assoc]

@[expose] def genRelB (X Y : Matrix (Fin 3) (Fin 3) (ZMod 8)) : Bool :=
  let A := ofMatrix X
  let B := ofMatrix Y
  let AB := mul A B
  isOne (mul A A) && isOne (mul (mul B B) B) && isOne (pow AB 7) &&
    isOne (pow (mul (mul AB A) (mul B B)) 4)

theorem genRelB_iff (X Y : Matrix (Fin 3) (Fin 3) (ZMod 8)) :
    genRelB X Y = true ↔ GenRel8 X Y := by
  simp only [genRelB, Bool.and_eq_true, isOne_iff, toMatrix_mul, toMatrix_pow, toMatrix_ofMatrix,
    GenRel8, and_assoc]

end Lift8

instance (X Y : Matrix (Fin 3) (Fin 3) (ZMod 8)) : Decidable (GenRel8 X Y) :=
  decidable_of_iff _ (Lift8.genRelB_iff X Y)

@[expose] def complement8A : Prop :=
  ∀ my : Fin 3 → Fin 3 → Bool, (Y8 + fourM my) * (Y8 + fourM my) * (Y8 + fourM my) = 1 →
    ∃ mk : Fin 3 → Fin 3 → Bool, (1 + fourM mk) * (Y8 + fourM my) = Y8 * (1 + fourM mk)

instance : Decidable complement8A := by
  unfold complement8A
  infer_instance

@[expose] def complement8B : Prop :=
  ∀ mx : Fin 3 → Fin 3 → Bool, GenRel8 (X8 + fourM mx) Y8 →
    ∃ mk : Fin 3 → Fin 3 → Bool, (1 + fourM mk) * Y8 = Y8 * (1 + fourM mk) ∧
      (1 + fourM mk) * (X8 + fourM mx) = X8 * (1 + fourM mk)

instance : Decidable complement8B := by
  unfold complement8B
  infer_instance

@[expose] def lift8Check (_ : Unit := ()) : Bool := decide complement8A && decide complement8B

end CFSG.OddStandard.AltStdSmall4.G2
