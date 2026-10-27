module

public import CFSG.HardMathSupport.Dickson.Sec6.HeisAux.F4Data
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Heis

open Matrix

variable {K : Type} [Field K] [CharP K 2] {ω : K}

@[expose] def ev (ω : K) : Fin 4 → K := ![0, 1, ω, ω + 1]

@[simp] theorem ev_zero : ev ω 0 = 0 := rfl
@[simp] theorem ev_one : ev ω 1 = 1 := rfl
@[simp] theorem ev_two : ev ω 2 = ω := rfl
@[simp] theorem ev_three : ev ω 3 = ω + 1 := rfl

theorem two_eq_zero_K : (2 : K) = 0 := CharP.cast_eq_zero K 2

theorem ev_add4 (a b : Fin 4) : ev ω (add4 a b) = ev ω a + ev ω b := by
  have h2 : (2 : K) = 0 := two_eq_zero_K
  fin_cases a <;> fin_cases b <;> simp [add4, ev, h2] <;> ring_nf <;> simp [h2]

theorem ev_mul4 (hω : ω ^ 2 + ω + 1 = 0) (a b : Fin 4) : ev ω (mul4 a b) = ev ω a * ev ω b := by
  have h2 : (2 : K) = 0 := two_eq_zero_K
  have hω2 : ω ^ 2 = ω + 1 := by linear_combination hω - h2 * (ω + 1)
  fin_cases a <;> fin_cases b <;> simp [mul4, ev, h2] <;> ring_nf <;> simp [hω2, h2] <;> ring_nf <;> simp [hω2, h2]

@[expose] def toMat (ω : K) (A : M3) : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => ev ω (A i j)

theorem toMat_apply (A : M3) (i j : Fin 3) : toMat ω A i j = ev ω (A i j) := rfl

theorem toMat_mmul (hω : ω ^ 2 + ω + 1 = 0) (A B : M3) :
    toMat ω (mmul A B) = toMat ω A * toMat ω B := by
  ext i k
  simp [toMat, mmul, Matrix.mul_apply, Fin.sum_univ_three, ev_add4, ev_mul4 hω]

theorem toMat_mone : toMat ω mone = 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [toMat, mone, ev]

theorem toMat_mpow (hω : ω ^ 2 + ω + 1 = 0) (A : M3) (n : ℕ) :
    toMat ω (mpow A n) = toMat ω A ^ n := by
  induction n with
  | zero => simp [mpow, toMat_mone]
  | succ n ih => rw [mpow, toMat_mmul hω, ih, pow_succ]

theorem det_toMat (hω : ω ^ 2 + ω + 1 = 0) (A : M3) : (toMat ω A).det = ev ω (mdet A) := by
  have h2 : (2 : K) = 0 := two_eq_zero_K
  have hneg : ∀ x : K, -x = x := fun x => by linear_combination (-x) * h2
  simp only [Matrix.det_fin_three, toMat_apply, mdet, ev_add4, ev_mul4 hω, sub_eq_add_neg, hneg]
  ring

theorem toMat_dM (hω : ω ^ 2 + ω + 1 = 0) (z : Fin 4) :
    toMat ω (dM z) = Matrix.diagonal ![1, ev ω z, ev ω z * ev ω z] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat_apply, dM, Matrix.diagonal_apply, ev_mul4 hω]

theorem toMat_CM (m : Fin 4) : toMat ω (CM m) = !![0, 0, ev ω m; 1, 0, 0; 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat_apply, CM]

end CFSG.HardMathSupport.Dickson.Sec6.Heis
