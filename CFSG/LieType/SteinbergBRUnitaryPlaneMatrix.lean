module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryTwoMatrix

public noncomputable section

namespace CFSG.LieType.SteinbergBR

open Matrix CFSG.ComponentClassification.CatalogueBUnitaryTwo
  CFSG.ComponentClassification.CatalogueBLinearTwoDescent CFSG.LieType.Universal.Unitary
open scoped MatrixGroups

universe u

variable {E : Type u} [Field E] (σ : E ≃+* E)

theorem hyperbolic_eqs {A : Matrix (Fin 2) (Fin 2) E}
    (hA : conjTr σ A * hyperbolicMatrix * A = hyperbolicMatrix) :
    σ (A 1 0) * A 0 0 + σ (A 0 0) * A 1 0 = 0 ∧ σ (A 1 0) * A 0 1 + σ (A 0 0) * A 1 1 = 1 ∧
      σ (A 1 1) * A 0 0 + σ (A 0 1) * A 1 0 = 1 ∧
      σ (A 1 1) * A 0 1 + σ (A 0 1) * A 1 1 = 0 := by
  have e : ∀ i j, (conjTr σ A * hyperbolicMatrix * A : Matrix (Fin 2) (Fin 2) E) i j =
      σ (A 1 i) * A 0 j + σ (A 0 i) * A 1 j := by
    intro i j
    simp [conjTr, hyperbolicMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  have h00 := congrFun₂ hA 0 0
  have h01 := congrFun₂ hA 0 1
  have h10 := congrFun₂ hA 1 0
  have h11 := congrFun₂ hA 1 1
  rw [e] at h00 h01 h10 h11
  simp only [hyperbolicMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h00 h01 h10 h11
  exact ⟨h00, h01, h10, h11⟩

theorem hyperbolic_entries {A : Matrix (Fin 2) (Fin 2) E}
    (hA : conjTr σ A * hyperbolicMatrix * A = hyperbolicMatrix) :
    σ (A 0 0) * A.det = A 0 0 ∧ σ (A 1 1) * A.det = A 1 1 ∧
      σ (A 0 1) * A.det = -A 0 1 ∧ σ (A 1 0) * A.det = -A 1 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := hyperbolic_eqs σ hA
  rw [Matrix.det_fin_two]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination A 0 0 * h2 - A 0 1 * h1
  · linear_combination A 1 1 * h3 - A 1 0 * h4
  · linear_combination A 0 0 * h4 - A 0 1 * h3
  · linear_combination A 1 1 * h1 - A 1 0 * h2

theorem fixed_div_of_rel {x c δ : E} (hc0 : c ≠ 0) (hc : σ c * δ = c)
    (hx : σ x * δ = x) : σ (c⁻¹ * x) = c⁻¹ * x := by
  have hσc : σ c ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hc
    exact hc0 hc.symm
  rw [map_mul, map_inv₀]
  field_simp
  linear_combination (-(σ x)) * hc + (σ c) * hx

variable {σ}

theorem fixed_conj_of_isometry {A : Matrix (Fin 2) (Fin 2) E}
    (hA : conjTr σ A * hyperbolicMatrix * A = hyperbolicMatrix) {t : Eˣ}
    (ht : σ (t : E) = -(t : E)) {c : E} (hc0 : c ≠ 0) (hc : σ c * A.det = c) (i j : Fin 2) :
    σ ((c⁻¹ • conjugatedMatrix t A) i j) = (c⁻¹ • conjugatedMatrix t A) i j := by
  obtain ⟨h00, h11, h01, h10⟩ := hyperbolic_entries σ hA
  have ht0 : (t : E) ≠ 0 := t.ne_zero
  fin_cases i <;> fin_cases j <;>
    simp only [conjugatedMatrix, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      smul_eq_mul, Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · exact fixed_div_of_rel σ hc0 hc h00
  · refine fixed_div_of_rel σ hc0 hc ?_
    rw [map_div₀, ht]
    field_simp
    linear_combination (-1 : E) * h01
  · refine fixed_div_of_rel σ hc0 hc ?_
    rw [map_mul, ht]
    linear_combination (-(t : E)) * h10
  · exact fixed_div_of_rel σ hc0 hc h11

theorem isometry_of_fixed {α β γ ε : E} (hα : σ α = α) (hβ : σ β = β) (hγ : σ γ = γ)
    (hε : σ ε = ε) {t : Eˣ} (ht : σ (t : E) = -(t : E)) {c : E}
    (hc : c * σ c * (α * ε - β * γ) = 1) :
    conjTr σ (c • !![α, β * (t : E); γ / (t : E), ε]) * hyperbolicMatrix *
      (c • !![α, β * (t : E); γ / (t : E), ε]) = hyperbolicMatrix := by
  have ht0 : (t : E) ≠ 0 := t.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, hyperbolicMatrix, Matrix.mul_apply, Fin.sum_univ_two, map_mul, map_div₀,
      hα, hβ, hγ, hε, ht]
  · field_simp
    ring
  · field_simp
    linear_combination hc
  · field_simp
    linear_combination hc
  · field_simp
    ring

end CFSG.LieType.SteinbergBR
