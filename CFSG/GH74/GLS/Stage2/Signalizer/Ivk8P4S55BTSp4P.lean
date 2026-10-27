module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTSp4L

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BS4

open Matrix

variable {F : Type} [Field F]

abbrev e0 : Fin 2 ⊕ Fin 2 → F := Pi.single (Sum.inl 0) 1

abbrev midB (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2) (Fin 2) F :=
  M.submatrix ![Sum.inl 1, Sum.inr 1] ![Sum.inl 1, Sum.inr 1]

section Entries

variable {M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}

theorem col_e0 (h : M *ᵥ e0 = e0) : M (Sum.inl 0) (Sum.inl 0) = 1 ∧
    M (Sum.inl 1) (Sum.inl 0) = 0 ∧ M (Sum.inr 0) (Sum.inl 0) = 0 ∧
    M (Sum.inr 1) (Sum.inl 0) = 0 := by
  have e := fun i => congrFun h i
  simp only [mulVec_single_one] at e
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using e (Sum.inl 0)
  · simpa using e (Sum.inl 1)
  · simpa using e (Sum.inr 0)
  · simpa using e (Sum.inr 1)

theorem row_e0 (h : M *ᵥ e0 = e0) (hsp : Mᵀ * jJ * M = jJ) : M (Sum.inr 0) (Sum.inl 1) = 0 ∧
    M (Sum.inr 0) (Sum.inr 1) = 0 ∧ M (Sum.inr 0) (Sum.inr 0) = 1 := by
  obtain ⟨c0, c1, c2, c3⟩ := col_e0 h
  have e := fun j => congrFun (congrFun hsp (Sum.inl 0)) j
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, transpose_apply, c0, c1,
    c2, c3] at e
  refine ⟨?_, ?_, ?_⟩
  · simpa using e (Sum.inl 1)
  · simpa using e (Sum.inr 1)
  · simpa using e (Sum.inr 0)

theorem det_midB (h : M *ᵥ e0 = e0) (hsp : Mᵀ * jJ * M = jJ) : (midB M).det = 1 := by
  obtain ⟨c0, c1, c2, c3⟩ := col_e0 h
  obtain ⟨r1, r2, r3⟩ := row_e0 h hsp
  have e := congrFun (congrFun hsp (Sum.inl 1)) (Sum.inr 1)
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, transpose_apply] at e
  simp [r1, r2] at e
  rw [det_fin_two]
  simp only [submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination e

theorem midB_mul (hM : M (Sum.inl 1) (Sum.inl 0) = 0 ∧ M (Sum.inr 1) (Sum.inl 0) = 0)
    (hN : N (Sum.inr 0) (Sum.inl 1) = 0 ∧ N (Sum.inr 0) (Sum.inr 1) = 0) :
    midB (M * N) = midB M * midB N := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Fin.sum_univ_two, Fintype.sum_sum_type]
  fin_cases i <;> fin_cases j <;> simp [hM.1, hM.2, hN.1, hN.2]

theorem eq_one_of_midB_eq_one (h2 : (2 : F) ≠ 0) (h : M *ᵥ e0 = e0) (hsp : Mᵀ * jJ * M = jJ)
    (hsq : M * M = 1) (hmid : midB M = 1) : M = 1 := by
  obtain ⟨c0, c1, c2, c3⟩ := col_e0 h
  obtain ⟨r1, r2, r3⟩ := row_e0 h hsp
  have m := fun i j => congrFun (congrFun hmid i) j
  have m00 : M (Sum.inl 1) (Sum.inl 1) = 1 := by simpa using m 0 0
  have m01 : M (Sum.inl 1) (Sum.inr 1) = 0 := by simpa using m 0 1
  have m10 : M (Sum.inr 1) (Sum.inl 1) = 0 := by simpa using m 1 0
  have m11 : M (Sum.inr 1) (Sum.inr 1) = 1 := by simpa using m 1 1
  have s := fun i j => congrFun (congrFun hsq i) j
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at s
  have two : ∀ y : F, 2 * y = 0 → y = 0 := fun y hy => (mul_eq_zero.mp hy).resolve_left h2
  have ha : M (Sum.inl 0) (Sum.inl 1) = 0 := by
    have := s (Sum.inl 0) (Sum.inl 1)
    simp [c0, r1, m00, m10] at this
    exact two _ (by linear_combination this)
  have hb : M (Sum.inl 0) (Sum.inr 1) = 0 := by
    have := s (Sum.inl 0) (Sum.inr 1)
    simp [c0, r2, m01, m11] at this
    exact two _ (by linear_combination this)
  have hd : M (Sum.inl 1) (Sum.inr 0) = 0 := by
    have := s (Sum.inl 1) (Sum.inr 0)
    simp [c1, r3, m00, m01] at this
    exact two _ (by linear_combination this)
  have he : M (Sum.inr 1) (Sum.inr 0) = 0 := by
    have := s (Sum.inr 1) (Sum.inr 0)
    simp [c3, r3, m10, m11] at this
    exact two _ (by linear_combination this)
  have hc : M (Sum.inl 0) (Sum.inr 0) = 0 := by
    have := s (Sum.inl 0) (Sum.inr 0)
    simp [c0, r3, ha, hb, hd, he] at this
    exact two _ (by linear_combination this)
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [c0, c1, c2, c3, r1, r2, r3, m00, m01, m10, m11, ha, hb, hc, hd, he]

end Entries

end BS4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
