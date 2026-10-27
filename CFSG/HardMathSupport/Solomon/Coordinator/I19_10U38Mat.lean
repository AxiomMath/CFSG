module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

open Matrix

namespace CFSG.HardMathSupport.Solomon.Coordinator.U38

variable {K : Type*} [Field K]

@[expose] def mA (ω : K) : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2]
@[expose] def mAi (ω : K) : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, ω ^ 2, 0; 0, 0, ω]
@[expose] def mP : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 1, 0, 0; 0, 1, 0]
@[expose] def mPi : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 0, 0, 1; 1, 0, 0]
@[expose] def mF (ω : K) : Matrix (Fin 3) (Fin 3) K := !![1, 1, 1; 1, ω, ω ^ 2; 1, ω ^ 2, ω]
@[expose] def mFi (ω : K) : Matrix (Fin 3) (Fin 3) K := !![1, 1, 1; 1, ω ^ 2, ω; 1, ω, ω ^ 2]
@[expose] def mQ (ω : K) : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, ω, 0; 0, 0, 1]
@[expose] def mQi (ω : K) : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, ω ^ 2, 0; 0, 0, 1]
@[expose] def mR (ω : K) : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, 1, 0; 0, 0, ω ^ 2]
@[expose] def mRi (ω : K) : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, 1, 0; 0, 0, ω]

section Alg

variable (ω : K) (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0)
include hω h2

theorem mA_mAi : mA ω * mAi ω = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mA, mAi, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.one_apply] <;> grind

theorem mAi_mA : mAi ω * mA ω = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mA, mAi, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.one_apply] <;> grind

omit hω h2 in
theorem mP_mPi : (mP : Matrix (Fin 3) (Fin 3) K) * mPi = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mP, mPi, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.one_apply]

omit hω h2 in
theorem mPi_mP : (mPi : Matrix (Fin 3) (Fin 3) K) * mP = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mP, mPi, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.one_apply]

theorem mF_mFi : mF ω * mFi ω = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mF, mFi, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.one_apply] <;> grind

theorem mFi_mF : mFi ω * mF ω = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mF, mFi, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.one_apply] <;> grind

theorem mQ_mQi : mQ ω * mQi ω = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mQ, mQi, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.one_apply] <;> grind

theorem mQi_mQ : mQi ω * mQ ω = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mQ, mQi, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.one_apply] <;> grind

theorem mR_mRi : mR ω * mRi ω = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mR, mRi, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.one_apply] <;> grind

theorem mRi_mR : mRi ω * mR ω = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mR, mRi, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.one_apply] <;> grind

theorem mA_mP : mA ω * mP = ω • (mP * mA ω) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mA, mP, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem mA_mP_eq_conj_Q : mA ω * mP = mQ ω * mP * mQi ω := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mA, mP, mQ, mQi, Matrix.mul_apply, Fin.sum_univ_three] <;>
    grind

theorem mA_mP_sq_eq_conj_R : mA ω * (mP * mP) = mR ω * (mP * mP) * mRi ω := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mA, mP, mR, mRi, Matrix.mul_apply, Fin.sum_univ_three] <;>
    grind

theorem mF_mP : mF ω * mP = mA ω * mF ω := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mA, mP, mF, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem det_mA : (mA ω).det = 1 := by
  have : mA ω = Matrix.diagonal ![1, ω, ω ^ 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mA]
  rw [this, Matrix.det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Fin.isValue]
  grind

omit hω h2 in
theorem det_mP : (mP : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [mP, Matrix.det_fin_three]

end Alg

section Unitary

variable (ω : K) (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) (bar : K →+* K)
  (hb : bar ω = ω ^ 2)
include hω h2 hb

theorem map_bar_pow2 : bar (ω ^ 2) = ω := by
  rw [map_pow, hb]
  grind

theorem unitary_mA : ((mA ω).map bar)ᵀ * mA ω = 1 := by
  have h4 : bar (ω ^ 2) = ω := map_bar_pow2 ω hω h2 bar hb
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mA, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.one_apply, h4, hb] <;> grind

theorem unitary_mP : (((mP : Matrix (Fin 3) (Fin 3) K)).map bar)ᵀ * mP = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mP, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.one_apply]

theorem unitary_mF : ((mF ω).map bar)ᵀ * mF ω = 1 := by
  have h4 : bar (ω ^ 2) = ω := map_bar_pow2 ω hω h2 bar hb
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mF, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.one_apply, h4, hb] <;> grind

theorem unitary_mQ : ((mQ ω).map bar)ᵀ * mQ ω = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mQ, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.one_apply, hb] <;> grind

theorem unitary_mR : ((mR ω).map bar)ᵀ * mR ω = 1 := by
  have h4 : bar (ω ^ 2) = ω := map_bar_pow2 ω hω h2 bar hb
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mR, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.one_apply, h4, hb] <;> grind

end Unitary

section GLUnits

variable (ω : K) (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0)

@[expose] def glA : Matrix.GeneralLinearGroup (Fin 3) K := ⟨mA ω, mAi ω, mA_mAi ω hω h2, mAi_mA ω hω h2⟩
@[expose] def glP : Matrix.GeneralLinearGroup (Fin 3) K := ⟨mP, mPi, mP_mPi, mPi_mP⟩
@[expose] def glF : Matrix.GeneralLinearGroup (Fin 3) K := ⟨mF ω, mFi ω, mF_mFi ω hω h2, mFi_mF ω hω h2⟩
@[expose] def glQ : Matrix.GeneralLinearGroup (Fin 3) K := ⟨mQ ω, mQi ω, mQ_mQi ω hω h2, mQi_mQ ω hω h2⟩
@[expose] def glR : Matrix.GeneralLinearGroup (Fin 3) K := ⟨mR ω, mRi ω, mR_mRi ω hω h2, mRi_mR ω hω h2⟩

end GLUnits

end CFSG.HardMathSupport.Solomon.Coordinator.U38
