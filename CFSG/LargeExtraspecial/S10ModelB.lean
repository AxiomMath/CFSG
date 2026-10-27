module

public import CFSG.LargeExtraspecial.S10Model

public section

namespace CFSG.LargeExtraspecial.S10

@[expose, irreducible] def u2 : SL2 := ⟨!![1, 1; 0, 1], by decide +kernel⟩

@[expose, irreducible] def τ₁ : Gm := (u2, 1)

@[expose, irreducible] def τ₂ : Gm := (1, u2)

@[expose] def Γ₁ : Subgroup Gm := (⊤ : Subgroup SL2).prod ⊥

@[expose] def Γ₂ : Subgroup Gm := (⊥ : Subgroup SL2).prod ⊤

theorem mem_Γ₁ {γ : Gm} : γ ∈ Γ₁ ↔ γ.2 = 1 := by
  simp [Γ₁, Subgroup.mem_prod]

theorem mem_Γ₂ {γ : Gm} : γ ∈ Γ₂ ↔ γ.1 = 1 := by
  simp [Γ₂, Subgroup.mem_prod]

theorem τ₁_mem_Γ₁ : τ₁ ∈ Γ₁ := mem_Γ₁.mpr (by decide +kernel)

theorem τ₂_mem_Γ₂ : τ₂ ∈ Γ₂ := mem_Γ₂.mpr (by decide +kernel)

theorem τ₁_ne_one : τ₁ ≠ 1 := by decide +kernel

theorem τ₂_ne_one : τ₂ ≠ 1 := by decide +kernel

theorem τ₁_sq : τ₁ * τ₁ = 1 := by decide +kernel

theorem τ₂_sq : τ₂ * τ₂ = 1 := by decide +kernel

theorem τ₁_τ₂_comm : τ₁ * τ₂ = τ₂ * τ₁ := by decide +kernel

theorem act_E00_iff : ∀ γ : Gm, act γ E00 = E00 ↔ γ = 1 ∨ γ = τ₁ ∨ γ = τ₂ ∨ γ = τ₁ * τ₂ := by
  decide +kernel

theorem Γ₁_closure : ∀ γ : Gm, γ.2 = 1 → ∃ δ₁ δ₂ : Gm,
    γ = δ₁ * τ₁ * δ₁⁻¹ ∨ γ = (δ₁ * τ₁ * δ₁⁻¹) * (δ₂ * τ₁ * δ₂⁻¹) := by
  decide +kernel

theorem Γ₂_closure : ∀ γ : Gm, γ.1 = 1 → ∃ δ₁ δ₂ : Gm,
    γ = δ₁ * τ₂ * δ₁⁻¹ ∨ γ = (δ₁ * τ₂ * δ₁⁻¹) * (δ₂ * τ₂ * δ₂⁻¹) := by
  decide +kernel

theorem diag_closure : ∀ s : Gm, s ^ 3 = 1 → ∃ δ₁ δ₂ : Gm,
    s = (δ₁ * (τ₁ * τ₂) * δ₁⁻¹) * (δ₂ * (τ₁ * τ₂) * δ₂⁻¹) := by
  decide +kernel

theorem conj_mem_Γ₁ : ∀ γ δ : Gm, γ.2 = 1 → (δ * γ * δ⁻¹).2 = 1 := by decide +kernel

theorem fpf_Γ₁ : ∀ s : Gm, s.2 = 1 → s ^ 3 = 1 → s ≠ 1 → ∀ m : M2, act s m = m → m = 0 := by
  decide +kernel

theorem τ₁_inv : ∀ s : Gm, s.2 = 1 → s ^ 3 = 1 → τ₁ * s * τ₁⁻¹ = s⁻¹ := by decide +kernel

theorem τ₂_inv : ∀ s : Gm, s.1 = 1 → s ^ 3 = 1 → τ₂ * s * τ₂⁻¹ = s⁻¹ := by decide +kernel

theorem comm_τ₁ : ∀ s : Gm, s ^ 3 = 1 → s * τ₁ = τ₁ * s → s.1 = 1 := by decide +kernel

theorem comm_τ₂ : ∀ s : Gm, s ^ 3 = 1 → s * τ₂ = τ₂ * s → s.2 = 1 := by decide +kernel

theorem comm_τ₁τ₂ : ∀ s : Gm, s ^ 3 = 1 → s * (τ₁ * τ₂) = (τ₁ * τ₂) * s → s = 1 := by
  decide +kernel

theorem exists_pf_eq_one : ∃ s : Gm, s ^ 3 = 1 ∧ pf E00 (act s E00) = 1 := by decide +kernel

end CFSG.LargeExtraspecial.S10
