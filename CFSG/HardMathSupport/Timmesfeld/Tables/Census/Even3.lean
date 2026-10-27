module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Klein

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open Matrix CFSG.Open

variable {K : Type} [Field K]

@[expose] def mD1 : Matrix (Fin 3) (Fin 3) K := !![1, 0, 1; 0, 1, 0; 0, 0, 1]

@[expose] def mD2 : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, 1, 1; 0, 0, 1]

@[expose] def mC : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 1, 1, 0; 0, 0, 1]

@[expose] def mCi : Matrix (Fin 3) (Fin 3) K := !![1, 1, 0; 1, 0, 0; 0, 0, 1]

variable (h2 : (1 : K) + 1 = 0)
include h2

theorem mD1_mul_self : (mD1 : Matrix (Fin 3) (Fin 3) K) * mD1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mD1, Matrix.mul_apply, Fin.sum_univ_three, h2]

theorem mD2_mul_self : (mD2 : Matrix (Fin 3) (Fin 3) K) * mD2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mD2, Matrix.mul_apply, Fin.sum_univ_three, h2]

omit h2 in
theorem mD_comm : (mD1 : Matrix (Fin 3) (Fin 3) K) * mD2 = mD2 * mD1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mD1, mD2, Matrix.mul_apply, Fin.sum_univ_three]

theorem mC_mul_mCi : (mC : Matrix (Fin 3) (Fin 3) K) * mCi = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mC, mCi, Matrix.mul_apply, Fin.sum_univ_three, h2]

theorem mCi_mul_mC : (mCi : Matrix (Fin 3) (Fin 3) K) * mC = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mC, mCi, Matrix.mul_apply, Fin.sum_univ_three, h2]

theorem mC_pow_three : (mC : Matrix (Fin 3) (Fin 3) K) * mC * mC = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mC, Matrix.mul_apply, Fin.sum_univ_three, h2]

theorem mC_conj_D1 : (mC : Matrix (Fin 3) (Fin 3) K) * mD1 * mCi = mD2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mC, mD1, mD2, mCi, Matrix.mul_apply, Fin.sum_univ_three, h2]

theorem mC_conj_D2 : (mC : Matrix (Fin 3) (Fin 3) K) * mD2 * mCi = mD1 * mD2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mC, mD1, mD2, mCi, Matrix.mul_apply, Fin.sum_univ_three, h2]

theorem neg_one_eq_one_of_two : (-1 : K) = 1 := by
  rw [neg_eq_iff_add_eq_zero]
  exact h2

@[expose] def glD1 : GL (Fin 3) K :=
  ⟨mD1, mD1, mD1_mul_self h2, mD1_mul_self h2⟩

@[expose] def glD2 : GL (Fin 3) K :=
  ⟨mD2, mD2, mD2_mul_self h2, mD2_mul_self h2⟩

@[expose] def glC : GL (Fin 3) K :=
  ⟨mC, mCi, mC_mul_mCi h2, mCi_mul_mC h2⟩

omit h2 in
theorem det_mD1 : (mD1 : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [mD1, det_fin_three]

omit h2 in
theorem det_mD2 : (mD2 : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [mD2, det_fin_three]

theorem det_mC : (mC : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [mC, det_fin_three, neg_one_eq_one_of_two h2]

theorem glD1_mem : glD1 h2 ∈ StatedSL 3 K := Subgroup.subset_closure (det_mD1)
theorem glD2_mem : glD2 h2 ∈ StatedSL 3 K := Subgroup.subset_closure (det_mD2)
theorem glC_mem : glC h2 ∈ StatedSL 3 K := Subgroup.subset_closure (det_mC h2)

theorem threeTwoWitness_statedProj_psl_three_even [Finite K] :
    ThreeTwoWitness (StatedProj (StatedSL 3 K)) := by
  refine threeTwoWitness_statedProj_klein (glD1 h2) (glD2 h2) (glC h2) (glD1_mem h2)
    (glD2_mem h2) (glC_mem h2) (Units.ext (mD1_mul_self h2)) (Units.ext (mD2_mul_self h2))
    (Units.ext mD_comm) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    have := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 2) hu
    simp [glD1, mD1, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at this
  · refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    show mC ^ 3 = 1
    rw [pow_succ, pow_two]
    exact mC_pow_three h2
  · intro u hu
    have := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 1) hu
    simp [glC, mC, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at this
  · refine Units.ext ?_
    show mC * mD1 * mCi = mD2
    exact mC_conj_D1 h2
  · refine Units.ext ?_
    show mC * mD2 * mCi = mD1 * mD2
    exact mC_conj_D2 h2

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
