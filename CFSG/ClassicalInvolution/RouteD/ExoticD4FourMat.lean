module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Reflection

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open Matrix CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def mB : Matrix (Fin 2) (Fin 2) F := !![0, -1; 1, 0]

@[expose] def mW (a b : F) : Matrix (Fin 2) (Fin 2) F := !![a, b; b, -a]

@[expose] def mVec (a b : F) : Fin 4 → Matrix (Fin 2) (Fin 2) F := ![1, mB, mW a b, mW a b * mB]

theorem det_mB : (mB : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  simp [mB, Matrix.det_fin_two_of]

theorem det_mW {a b : F} (hab : a ^ 2 + b ^ 2 = -1) : (mW a b).det = 1 := by
  simp only [mW, Matrix.det_fin_two_of]
  linear_combination (-1 : F) * hab

theorem mB_mul_mB : (mB : Matrix (Fin 2) (Fin 2) F) * mB = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mB, Matrix.mul_apply, Fin.sum_univ_two]

theorem mW_mul_mW {a b : F} (hab : a ^ 2 + b ^ 2 = -1) : mW a b * mW a b = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mW, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination hab
  · ring
  · ring
  · linear_combination hab

theorem mB_mul_mW (a b : F) : mB * mW a b = -(mW a b * mB) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mB, mW, Matrix.mul_apply, Fin.sum_univ_two]

theorem mB_mul_mW_mul_mB (a b : F) : mB * mW a b * mB = mW a b := by
  rw [mB_mul_mW, neg_mul, mul_assoc, mB_mul_mB]
  simp

theorem det_mWB {a b : F} (hab : a ^ 2 + b ^ 2 = -1) : (mW a b * mB).det = 1 := by
  rw [Matrix.det_mul, det_mW hab, det_mB, one_mul]

theorem det_mVec {a b : F} (hab : a ^ 2 + b ^ 2 = -1) (j : Fin 4) : (mVec a b j).det = 1 := by
  fin_cases j
  · simp [mVec]
  · simpa [mVec] using det_mB
  · simpa [mVec] using det_mW hab
  · simpa [mVec] using det_mWB hab

theorem mWB_eq (a b : F) : mW a b * mB = !![b, -a; -a, -b] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mB, mW, Matrix.mul_apply, Fin.sum_univ_two]

theorem mVec_zero (a b : F) : mVec a b 0 = 1 := rfl

theorem mVec_one (a b : F) : mVec a b 1 = mB := rfl

theorem mVec_two (a b : F) : mVec a b 2 = mW a b := rfl

theorem mVec_three (a b : F) : mVec a b 3 = mW a b * mB := rfl

theorem polarDet_mVec {a b : F} (hab : a ^ 2 + b ^ 2 = -1) (j k : Fin 4) :
    polarDet (mVec a b j) (mVec a b k) = if j = k then 2 else 0 := by
  fin_cases j <;> fin_cases k <;>
    simp [mVec_zero, mVec_one, mVec_two, mVec_three, polarDet, mB, mW] <;> ring_nf <;>
    first | rfl | (linear_combination (-2 : F) * hab)

theorem mW_mul_mVec {a b : F} (hab : a ^ 2 + b ^ 2 = -1) :
    mW a b * mVec a b 0 = mVec a b 2 ∧ mW a b * mVec a b 1 = mVec a b 3 ∧
      mW a b * mVec a b 2 = -mVec a b 0 ∧ mW a b * mVec a b 3 = -mVec a b 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [mVec_zero, mVec_two]
  · simp [mVec_one, mVec_three]
  · rw [mVec_two, mVec_zero, mW_mul_mW hab]
  · rw [mVec_three, mVec_one, ← mul_assoc, mW_mul_mW hab]
    simp

@[expose] def sgnB (F : Type) [Field F] : Fin 4 → F := ![-1, -1, 1, 1]

theorem mB_mul_mVec_mul_mB (a b : F) (j : Fin 4) :
    mB * mVec a b j * mB = sgnB F j • mVec a b j := by
  fin_cases j
  · simp [mVec_zero, sgnB, mB_mul_mB]
  · have : (mB : Matrix (Fin 2) (Fin 2) F) * mB * mB = -mB := by
      rw [mB_mul_mB]
      simp
    simpa [mVec_one, sgnB] using this
  · simpa [mVec_two, sgnB] using mB_mul_mW_mul_mB a b
  · have : mB * (mW a b * mB) * mB = mW a b * mB := by
      rw [← mul_assoc, mB_mul_mW_mul_mB]
    simpa [mVec_three, sgnB] using this

end CFSG.ClassicalInvolution.RouteD.Exotic
