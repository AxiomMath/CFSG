module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagLb

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace DiagL

open Matrix

variable {F : Type*} [Field F]

local macro "kb_norm" : tactic =>
  `(tactic| (
    simp only [uK, lK, kZero, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.zero_eta,
      Fin.mk_one, Matrix.map_apply, zero_mul, mul_zero, map_zero, map_one]
    ring1))

theorem blockScalar_of_comm {l : F} {X : Matrix (Fin 4) (Fin 4) F}
    (h1 : X * uK l 1 0 = uK l 1 0 * X) (h2 : X * lK l 1 0 = lK l 1 0 * X) :
    X 0 2 = 0 ∧ X 0 3 = 0 ∧ X 1 2 = 0 ∧ X 1 3 = 0 ∧ X 2 0 = 0 ∧ X 2 1 = 0 ∧ X 3 0 = 0 ∧
      X 3 1 = 0 ∧ X 2 2 = X 0 0 ∧ X 2 3 = X 0 1 ∧ X 3 2 = X 1 0 ∧ X 3 3 = X 1 1 := by
  have E1 := fun i j => congrFun (congrFun h1 i) j
  have E2 := fun i j => congrFun (congrFun h2 i) j
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (norm := kb_norm) E2 0 0
  · linear_combination (norm := kb_norm) E2 0 1
  · linear_combination (norm := kb_norm) E2 1 0
  · linear_combination (norm := kb_norm) E2 1 1
  · linear_combination (norm := kb_norm) E1 2 2
  · linear_combination (norm := kb_norm) E1 2 3
  · linear_combination (norm := kb_norm) E1 3 2
  · linear_combination (norm := kb_norm) E1 3 3
  · linear_combination (norm := kb_norm) -E1 0 2
  · linear_combination (norm := kb_norm) -E1 0 3
  · linear_combination (norm := kb_norm) -E1 1 2
  · linear_combination (norm := kb_norm) -E1 1 3

theorem eq_of_comm_uK {l : F} (hl : l ≠ 0) {X : Matrix (Fin 4) (Fin 4) F}
    (h1 : X * uK l 1 0 = uK l 1 0 * X) (h2 : X * lK l 1 0 = lK l 1 0 * X)
    (h3 : X * uK l 0 1 = uK l 0 1 * X) : X = X 0 0 • 1 + X 1 0 • kZero l := by
  obtain ⟨e02, e03, e12, e13, e20, e21, e30, e31, e22, e23, e32, e33⟩ := blockScalar_of_comm h1 h2
  have E3 := fun i j => congrFun (congrFun h3 i) j
  have h01 : X 0 1 = l * X 1 0 := by
    linear_combination (norm := kb_norm) E3 0 2 + l * e32
  have h11 : X 1 1 = X 0 0 := by
    have : l * X 1 1 = l * X 0 0 := by linear_combination (norm := kb_norm) -E3 0 3 - l * e33
    exact mul_left_cancel₀ hl this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kZero] <;>
    first
      | assumption
      | linear_combination h01
      | linear_combination h11
      | linear_combination e22
      | linear_combination e23 + h01
      | linear_combination e32
      | linear_combination e33 + h11

theorem eq_of_semilinear_comm_uK {l : F} (hl : l ≠ 0) {B : Matrix (Fin 4) (Fin 4) F}
    (hB : IsUnit B.det) (σ : F →+* F)
    (h1 : B * (uK l 1 0).map σ = uK l 1 0 * B) (h2 : B * (lK l 1 0).map σ = lK l 1 0 * B)
    (h3 : B * (uK l 0 1).map σ = uK l 0 1 * B)
    (h4 : ∀ c : F, B * (uK l c 0).map σ = uK l c 0 * B) :
    (∀ c, σ c = c) ∧ B = B 0 0 • 1 + B 1 0 • kZero l := by
  have hu1 : (uK l 1 0).map σ = uK l 1 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uK]
  have hl1 : (lK l 1 0).map σ = lK l 1 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lK]
  rw [hu1] at h1
  rw [hl1] at h2
  obtain ⟨e02, e03, e12, e13, e20, e21, e30, e31, e22, e23, e32, e33⟩ := blockScalar_of_comm h1 h2
  have hσ : ∀ c, σ c = c := by
    intro c
    have E := fun i j => congrFun (congrFun (h4 c) i) j
    have k02 : B 0 0 * σ c = c * B 0 0 := by linear_combination (norm := kb_norm) E 0 2 + c * e22
    have k03 : B 0 1 * σ c = c * B 0 1 := by linear_combination (norm := kb_norm) E 0 3 + c * e23
    have k12 : B 1 0 * σ c = c * B 1 0 := by linear_combination (norm := kb_norm) E 1 2 + c * e32
    have k13 : B 1 1 * σ c = c * B 1 1 := by linear_combination (norm := kb_norm) E 1 3 + c * e33
    by_contra hne
    have hsub : σ c - c ≠ 0 := sub_ne_zero.mpr hne
    have z00 : B 0 0 = 0 := by
      have : B 0 0 * (σ c - c) = 0 := by linear_combination k02
      exact (mul_eq_zero.1 this).resolve_right hsub
    have z01 : B 0 1 = 0 := by
      have : B 0 1 * (σ c - c) = 0 := by linear_combination k03
      exact (mul_eq_zero.1 this).resolve_right hsub
    have z10 : B 1 0 = 0 := by
      have : B 1 0 * (σ c - c) = 0 := by linear_combination k12
      exact (mul_eq_zero.1 this).resolve_right hsub
    have z11 : B 1 1 = 0 := by
      have : B 1 1 * (σ c - c) = 0 := by linear_combination k13
      exact (mul_eq_zero.1 this).resolve_right hsub
    have hdet : B.det = 0 := by
      rw [Matrix.det_succ_row_zero]
      simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove, z00,
        z01, e02, e03]
    rw [hdet] at hB
    exact not_isUnit_zero hB
  refine ⟨hσ, ?_⟩
  have hu3 : (uK l 0 1).map σ = uK l 0 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uK, hσ]
  rw [hu3] at h3
  exact eq_of_comm_uK hl h1 h2 h3

end DiagL

end CFSG.ComponentClassification.CatFactsL4U4
