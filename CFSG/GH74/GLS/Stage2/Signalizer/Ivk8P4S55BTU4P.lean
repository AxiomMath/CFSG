module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4F3
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTU4R

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BU4

open Matrix BS4 BL4

variable {K : Type} [Field K] {φ : K →+* K}

theorem col_e0c {M : MB K} {c : K} (h : M *ᵥ e0 = c • e0) : M (Sum.inl 0) (Sum.inl 0) = c ∧
    M (Sum.inl 1) (Sum.inl 0) = 0 ∧ M (Sum.inr 0) (Sum.inl 0) = 0 ∧
    M (Sum.inr 1) (Sum.inl 0) = 0 := by
  have e := fun i => congrFun h i
  simp only [mulVec_single_one] at e
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using e (Sum.inl 0)
  · simpa using e (Sum.inl 1)
  · simpa using e (Sum.inr 0)
  · simpa using e (Sum.inr 1)

theorem row_e0U {M : MB K} {c : K} (h : M *ᵥ e0 = c • e0) (hu : (M.map φ)ᵀ * jU * M = jU) :
    M (Sum.inr 0) (Sum.inl 1) = 0 ∧ M (Sum.inr 0) (Sum.inr 1) = 0 ∧
      φ c * M (Sum.inr 0) (Sum.inr 0) = 1 := by
  obtain ⟨c0, c1, c2, c3⟩ := col_e0c h
  have e := fun j => congrFun (congrFun hu (Sum.inl 0)) j
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, transpose_apply,
    Matrix.map_apply, c0, c1, c2, c3] at e
  have h3 : φ c * M (Sum.inr 0) (Sum.inr 0) = 1 := by simpa using e (Sum.inr 0)
  have hc : φ c ≠ 0 := left_ne_zero_of_mul_eq_one h3
  have h1 : φ c * M (Sum.inr 0) (Sum.inl 1) = 0 := by simpa using e (Sum.inl 1)
  have h2 : φ c * M (Sum.inr 0) (Sum.inr 1) = 0 := by simpa using e (Sum.inr 1)
  exact ⟨(mul_eq_zero.mp h1).resolve_left hc, (mul_eq_zero.mp h2).resolve_left hc, h3⟩

theorem midB_one : midB (1 : MB K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

theorem eq_one_of_midB_eq_one' (h2 : (2 : K) ≠ 0) {M : MB K} (h : M *ᵥ e0 = e0)
    (hr : M (Sum.inr 0) (Sum.inl 1) = 0 ∧ M (Sum.inr 0) (Sum.inr 1) = 0 ∧
      M (Sum.inr 0) (Sum.inr 0) = 1) (hsq : M * M = 1) (hmid : midB M = 1) : M = 1 := by
  obtain ⟨c0, c1, c2, c3⟩ := col_e0 h
  obtain ⟨r1, r2, r3⟩ := hr
  have m := fun i j => congrFun (congrFun hmid i) j
  have m00 : M (Sum.inl 1) (Sum.inl 1) = 1 := by simpa using m 0 0
  have m01 : M (Sum.inl 1) (Sum.inr 1) = 0 := by simpa using m 0 1
  have m10 : M (Sum.inr 1) (Sum.inl 1) = 0 := by simpa using m 1 0
  have m11 : M (Sum.inr 1) (Sum.inr 1) = 1 := by simpa using m 1 1
  have s := fun i j => congrFun (congrFun hsq i) j
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at s
  have two : ∀ y : K, 2 * y = 0 → y = 0 := fun y hy => (mul_eq_zero.mp hy).resolve_left h2
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

end BU4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
