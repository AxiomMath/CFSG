module

public import CFSG.CGT.Timmesfeld75.SLTransvection

public section

namespace CFSG.CGT.Timmesfeld75

open Matrix
open scoped MatrixGroups

variable {F : Type*} [Field F] {n : ℕ}

theorem IsTransvection.exists_data {u : SL(n, F)} (hu : IsTransvection u) :
    ∃ (f : Module.Dual F (Fin n → F)) (v : Fin n → F), f v = 0 ∧ v ≠ 0 ∧
      ∀ x : Fin n → F, (u : Matrix (Fin n) (Fin n) F) *ᵥ x = x + f x • v := by
  obtain ⟨hu1, f, v, hfv, huf⟩ := hu
  have hne : LinearEquiv.transvection hfv ≠ 1 := by
    intro h
    apply hu1
    apply Matrix.SpecialLinearGroup.toLin'_injective
    rw [huf, h, map_one]
  obtain ⟨-, hv⟩ := ne_zero_of_transvection_ne_one hfv hne
  refine ⟨f, v, hfv, hv, fun x => ?_⟩
  have h1 := Matrix.SpecialLinearGroup.toLin'_apply u x
  rw [huf] at h1
  exact h1.symm.trans (LinearEquiv.transvection.apply hfv x)

theorem IsTransvection.commute_of_common_image {u₁ u₂ : SL(n, F)} (h₁ : IsTransvection u₁)
    (h₂ : IsTransvection u₂) {w x₁ x₂ : Fin n → F} (hw : w ≠ 0)
    (hx₁ : (u₁ : Matrix (Fin n) (Fin n) F) *ᵥ x₁ - x₁ = w)
    (hx₂ : (u₂ : Matrix (Fin n) (Fin n) F) *ᵥ x₂ - x₂ = w) : u₁ * u₂ = u₂ * u₁ := by
  obtain ⟨f₁, v₁, hfv₁, hv₁, hu₁⟩ := h₁.exists_data
  obtain ⟨f₂, v₂, hfv₂, hv₂, hu₂⟩ := h₂.exists_data
  have e₁ : f₁ x₁ • v₁ = w := by
    have := hu₁ x₁
    rw [this] at hx₁
    simpa using hx₁
  have e₂ : f₂ x₂ • v₂ = w := by
    have := hu₂ x₂
    rw [this] at hx₂
    simpa using hx₂
  have hc₁ : f₁ x₁ ≠ 0 := by
    intro h
    rw [h, zero_smul] at e₁
    exact hw e₁.symm
  have hc₂ : f₂ x₂ ≠ 0 := by
    intro h
    rw [h, zero_smul] at e₂
    exact hw e₂.symm
  have hv : v₂ = (f₂ x₂)⁻¹ • (f₁ x₁) • v₁ := by
    rw [e₁, ← e₂, smul_smul, inv_mul_cancel₀ hc₂, one_smul]
  have hf₁v₂ : f₁ v₂ = 0 := by
    rw [hv, map_smul, map_smul, hfv₁]
    simp
  have hv' : v₁ = (f₁ x₁)⁻¹ • (f₂ x₂) • v₂ := by
    rw [e₂, ← e₁, smul_smul, inv_mul_cancel₀ hc₁, one_smul]
  have hf₂v₁ : f₂ v₁ = 0 := by
    rw [hv', map_smul, map_smul, hfv₂]
    simp
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  simp only [Matrix.toLin'_apply]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hu₂ x, hu₁ x, hu₁, hu₂, map_add, map_add,
    map_smul, map_smul, hf₁v₂, hf₂v₁]
  simp only [smul_zero, add_zero]
  abel

end CFSG.CGT.Timmesfeld75
