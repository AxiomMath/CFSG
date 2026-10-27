module

public import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LieType.SeitzGeneration.HeisTensor.Words

open Matrix

variable {K : Type} [Field K] {n : ℕ}

variable {X Y : Matrix (Fin n) (Fin n) K} {ω α β : K}

theorem hA (hyx : Y * X = ω • (X * Y)) :
    ∀ Z : Matrix (Fin n) (Fin n) K, Y * (X * Z) = ω • (X * (Y * Z)) := by
  intro Z
  rw [← Matrix.mul_assoc, hyx, Matrix.smul_mul, Matrix.mul_assoc]

theorem hX3' (hX3 : X * X * X = α • 1) :
    ∀ Z : Matrix (Fin n) (Fin n) K, X * (X * (X * Z)) = α • Z := fun Z => by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hX3, Matrix.smul_mul, Matrix.one_mul]

theorem hX3'' (hX3 : X * X * X = α • 1) : X * (X * X) = α • (1 : Matrix (Fin n) (Fin n) K) := by
  rw [← Matrix.mul_assoc, hX3]

theorem idA (hω3 : ω ^ 3 = 1) (hyx : Y * X = ω • (X * Y)) (hX3 : X * X * X = α • 1)
    (hY3 : Y * Y * Y = β • 1) :
    (X * Y) * (X * Y) * (X * Y) = (α * β) • (1 : Matrix (Fin n) (Fin n) K) := by
  simp only [Matrix.mul_assoc, hA hyx, Matrix.mul_smul, Matrix.smul_mul, hX3' hX3, hX3' hY3,
    hX3'' hX3, hX3'' hY3, smul_smul]
  congr 1
  linear_combination (α * β) * hω3

theorem idB (hω3 : ω ^ 3 = 1) (hyx : Y * X = ω • (X * Y)) (hX3 : X * X * X = α • 1)
    (hY3 : Y * Y * Y = β • 1) :
    (X * (Y * Y)) * (X * (Y * Y)) * (X * (Y * Y)) =
      (α * β ^ 2) • (1 : Matrix (Fin n) (Fin n) K) := by
  simp only [Matrix.mul_assoc, hA hyx, Matrix.mul_smul, Matrix.smul_mul, hX3' hX3, hX3' hY3,
    hX3'' hX3, hX3'' hY3, smul_smul, Matrix.one_mul, Matrix.mul_one]
  congr 1
  linear_combination (α * β ^ 2) * hω3

theorem idC (hX3 : X * X * X = α • 1) (hY3 : Y * Y * Y = β • 1) :
    (X * (Y * Y)) * (Y * (X * X)) = (α * β) • (1 : Matrix (Fin n) (Fin n) K) := by
  simp only [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul, hX3' hX3, hX3' hY3,
    hX3'' hX3, hX3'' hY3, smul_smul, Matrix.one_mul, Matrix.mul_one]
  congr 1
  ring

theorem idD1 (hyx : Y * X = ω • (X * Y)) : Y * (X * Y) = ω • (X * (Y * Y)) := by
  simp only [Matrix.mul_assoc, hA hyx]

theorem idD2 (hω3 : ω ^ 3 = 1) (hyx : Y * X = ω • (X * Y)) (hY3 : Y * Y * Y = β • 1) :
    Y * ((X * Y) * (X * Y)) = β • (X * X) := by
  simp only [Matrix.mul_assoc, hA hyx, Matrix.mul_smul, Matrix.smul_mul, hX3' hY3,
    hX3'' hY3, smul_smul, Matrix.one_mul, Matrix.mul_one]
  congr 1
  linear_combination β * hω3

theorem idE1 (hyx : Y * X = ω • (X * Y)) (hY3 : Y * Y * Y = β • 1) :
    Y * (X * (Y * Y)) = (ω * β) • X := by
  simp only [Matrix.mul_assoc, hA hyx, Matrix.mul_smul, Matrix.smul_mul, hX3'' hY3, smul_smul,
    Matrix.one_mul, Matrix.mul_one]

theorem idE2 (hω3 : ω ^ 3 = 1) (hyx : Y * X = ω • (X * Y)) (hY3 : Y * Y * Y = β • 1) :
    Y * ((X * (Y * Y)) * (X * (Y * Y))) = β • ((X * Y) * (X * Y)) := by
  simp only [Matrix.mul_assoc, hA hyx, hyx, Matrix.mul_smul, Matrix.smul_mul, hX3' hY3,
    hX3'' hY3, smul_smul, Matrix.one_mul, Matrix.mul_one]
  congr 1
  linear_combination (ω * β) * hω3

theorem idF2 (hω3 : ω ^ 3 = 1) (hyx : Y * X = ω • (X * Y)) : X * Y = ω ^ 2 • (Y * X) := by
  rw [hyx, smul_smul]
  have : ω ^ 2 * ω = 1 := by linear_combination hω3
  rw [this, one_smul]

theorem idF3 (hω3 : ω ^ 3 = 1) (hyx : Y * X = ω • (X * Y)) :
    (X * Y) * Y = ω ^ 2 • (Y * (X * Y)) := by
  rw [idD1 hyx, smul_smul]
  have : ω ^ 2 * ω = 1 := by linear_combination hω3
  rw [this, one_smul, Matrix.mul_assoc]

theorem idF4 (hω3 : ω ^ 3 = 1) (hyx : Y * X = ω • (X * Y)) (hY3 : Y * Y * Y = β • 1) :
    (X * (Y * Y)) * Y = ω ^ 2 • (Y * (X * (Y * Y))) := by
  rw [idE1 hyx hY3, smul_smul]
  simp only [Matrix.mul_assoc, hX3'' hY3, Matrix.mul_smul, Matrix.mul_one]
  congr 1
  linear_combination (-β) * hω3

end CFSG.LieType.SeitzGeneration.HeisTensor.Words
