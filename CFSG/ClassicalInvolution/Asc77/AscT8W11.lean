module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterL4Mat
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.ClassicalInvolution.Asc77.T8W

open Matrix CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4

variable {F : Type} [Field F]

theorem shape_block0_zero (σ : F ≃+* F) (M : Matrix (Fin 4) (Fin 4) F) (hdet : M.det ≠ 0)
    (h01 : ∀ t : F, E01 t * M = M * E01 (σ t)) (h10 : ∀ t : F, E10 t * M = M * E10 (σ t)) :
    σ = RingEquiv.refl F ∧ ∃ a : F, a ≠ 0 ∧
      M = !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, M 2 2, M 2 3; 0, 0, M 3 2, M 3 3] := by
  have a01 := h01 1
  have a10 := h10 1
  rw [map_one] at a01 a10
  have m10 : M 1 0 = 0 := by
    have h := congrFun (congrFun a01 0) 0
    simp [E01, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m11 : M 1 1 = M 0 0 := by
    have h := congrFun (congrFun a01 0) 1
    simp [E01, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m12 : M 1 2 = 0 := by
    have h := congrFun (congrFun a01 0) 2
    simp [E01, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m13 : M 1 3 = 0 := by
    have h := congrFun (congrFun a01 0) 3
    simp [E01, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m20 : M 2 0 = 0 := by
    have h := congrFun (congrFun a01 2) 1
    simp [E01, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m30 : M 3 0 = 0 := by
    have h := congrFun (congrFun a01 3) 1
    simp [E01, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m01 : M 0 1 = 0 := by
    have h := congrFun (congrFun a10 1) 1
    simp [E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m02 : M 0 2 = 0 := by
    have h := congrFun (congrFun a10 1) 2
    simp [E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m03 : M 0 3 = 0 := by
    have h := congrFun (congrFun a10 1) 3
    simp [E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m21 : M 2 1 = 0 := by
    have h := congrFun (congrFun a10 2) 0
    simp [E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m31 : M 3 1 = 0 := by
    have h := congrFun (congrFun a10 3) 0
    simp [E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have hM : M = !![M 0 0, 0, 0, 0; 0, M 0 0, 0, 0; 0, 0, M 2 2, M 2 3; 0, 0, M 3 2, M 3 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [m10, m11, m12, m13, m20, m30, m01, m02, m03, m21, m31]
  have ha : M 0 0 ≠ 0 := by
    intro h0
    apply hdet
    refine Matrix.det_eq_zero_of_row_eq_zero 0 fun j => ?_
    fin_cases j <;> simp [h0, m01, m02, m03]
  have hσ : σ = RingEquiv.refl F := by
    ext t
    have h := congrFun (congrFun (h01 t) 0) 1
    simp [E01, Matrix.mul_apply, Fin.sum_univ_four] at h
    have h' : (t - σ t) * M 0 0 = 0 := by linear_combination h - t * m11
    have := (mul_eq_zero.mp h').resolve_right ha
    simpa using (sub_eq_zero.mp this).symm
  exact ⟨hσ, M 0 0, ha, hM⟩

theorem shape_block0_one (σ : F ≃+* F) (M : Matrix (Fin 4) (Fin 4) F) (hdet : M.det ≠ 0)
    (h01 : ∀ t : F, E01 t * M = M * E10 (-σ t)) (h10 : ∀ t : F, E10 t * M = M * E01 (-σ t)) :
    σ = RingEquiv.refl F ∧ ∃ m : F, m ≠ 0 ∧
      M = !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, M 2 2, M 2 3; 0, 0, M 3 2, M 3 3] := by
  have a01 := h01 1
  have a10 := h10 1
  rw [map_one] at a01 a10
  have m11 : M 1 1 = 0 := by
    have h := congrFun (congrFun a01 0) 1
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m12 : M 1 2 = 0 := by
    have h := congrFun (congrFun a01 0) 2
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m13 : M 1 3 = 0 := by
    have h := congrFun (congrFun a01 0) 3
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m21 : M 2 1 = 0 := by
    have h := congrFun (congrFun a01 2) 0
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m31 : M 3 1 = 0 := by
    have h := congrFun (congrFun a01 3) 0
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m10 : M 1 0 = -M 0 1 := by
    have h := congrFun (congrFun a01 0) 0
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m00 : M 0 0 = 0 := by
    have h := congrFun (congrFun a10 1) 0
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m02 : M 0 2 = 0 := by
    have h := congrFun (congrFun a10 1) 2
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m03 : M 0 3 = 0 := by
    have h := congrFun (congrFun a10 1) 3
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m20 : M 2 0 = 0 := by
    have h := congrFun (congrFun a10 2) 1
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have m30 : M 3 0 = 0 := by
    have h := congrFun (congrFun a10 3) 1
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    linear_combination h
  have hM : M = !![0, M 0 1, 0, 0; -M 0 1, 0, 0, 0; 0, 0, M 2 2, M 2 3; 0, 0, M 3 2, M 3 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [m00, m02, m03, m10, m11, m12, m13, m20, m21, m30, m31]
  have hm : M 0 1 ≠ 0 := by
    intro h0
    apply hdet
    refine Matrix.det_eq_zero_of_row_eq_zero 0 fun j => ?_
    fin_cases j <;> simp [h0, m00, m02, m03]
  have hσ : σ = RingEquiv.refl F := by
    ext t
    have h := congrFun (congrFun (h01 t) 0) 0
    simp [E01, E10, Matrix.mul_apply, Fin.sum_univ_four] at h
    have h' : (σ t - t) * M 0 1 = 0 := by linear_combination h - t * m10
    have := (mul_eq_zero.mp h').resolve_right hm
    simpa using sub_eq_zero.mp this
  exact ⟨hσ, M 0 1, hm, hM⟩

theorem exists_eigenbasis (h2 : (2 : F) ≠ 0) {a : F} (ha : a ≠ 0) (H : Matrix (Fin 2) (Fin 2) F)
    (hH2 : H * H = (a * a) • (1 : Matrix (Fin 2) (Fin 2) F))
    (hns : ¬ ∃ c : F, H = c • (1 : Matrix (Fin 2) (Fin 2) F)) :
    ∃ p q r s : F, p * s - q * r ≠ 0 ∧ H 0 0 * p + H 0 1 * q = a * p ∧
      H 1 0 * p + H 1 1 * q = a * q ∧ H 0 0 * r + H 0 1 * s = -(a * r) ∧
      H 1 0 * r + H 1 1 * s = -(a * s) := by
  have e00 := congrFun (congrFun hH2 0) 0
  have e01' := congrFun (congrFun hH2 0) 1
  have e10' := congrFun (congrFun hH2 1) 0
  have e11 := congrFun (congrFun hH2 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01' e10' e11
  by_cases h10 : H 1 0 = 0
  · by_cases h01 : H 0 1 = 0
    ·
      have hsq : (H 0 0 - H 1 1) * (H 0 0 + H 1 1) = 0 := by
        rw [h10, h01] at e00 e11
        linear_combination e00 - e11
      have hne : H 0 0 - H 1 1 ≠ 0 := by
        intro h
        apply hns
        refine ⟨H 0 0, ?_⟩
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h10, h01, sub_eq_zero.mp h]
      have htr : H 1 1 = -H 0 0 := by
        have := (mul_eq_zero.mp hsq).resolve_left hne
        linear_combination this
      have hsq0 : (H 0 0 - a) * (H 0 0 + a) = 0 := by
        rw [h10, h01] at e00
        linear_combination e00
      rcases mul_eq_zero.mp hsq0 with h | h
      · have hH00 : H 0 0 = a := by linear_combination h
        refine ⟨1, 0, 0, 1, by simp, ?_, ?_, ?_, ?_⟩ <;> simp [h10, h01, htr, hH00]
      · have hH00 : H 0 0 = -a := by linear_combination h
        refine ⟨0, 1, 1, 0, by simp, ?_, ?_, ?_, ?_⟩ <;> simp [h10, h01, htr, hH00]
    ·
      have htr : H 1 1 = -H 0 0 := by
        have h : H 0 1 * (H 0 0 + H 1 1) = 0 := by linear_combination e01'
        have := (mul_eq_zero.mp h).resolve_left h01
        linear_combination this
      refine ⟨H 0 1, H 1 1 + a, H 0 1, H 1 1 - a, ?_, ?_, ?_, ?_, ?_⟩
      · intro h
        have h' : (-2 * a) * H 0 1 = 0 := by linear_combination h
        exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h2) ha) h01 h'
      · linear_combination e01'
      · rw [h10] at e11 ⊢
        linear_combination e11
      · linear_combination e01'
      · rw [h10] at e11 ⊢
        linear_combination e11
  ·
    have htr : H 1 1 = -H 0 0 := by
      have h : H 1 0 * (H 0 0 + H 1 1) = 0 := by linear_combination e10'
      have := (mul_eq_zero.mp h).resolve_left h10
      linear_combination this
    refine ⟨H 0 0 + a, H 1 0, H 0 0 - a, H 1 0, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      have h' : (2 * a) * H 1 0 = 0 := by linear_combination h
      exact mul_ne_zero (mul_ne_zero h2 ha) h10 h'
    · linear_combination e00
    · linear_combination e10'
    · linear_combination e00
    · linear_combination e10'

end CFSG.ClassicalInvolution.Asc77.T8W
