module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDSetting

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup

variable {G : Type*} [Group G]

namespace Data

variable (d : Data G)

@[expose] def conjW (B : Subgroup G) : Subgroup G := B.map (MulAut.conj d.w₂).toMonoidHom

end Data

structure HypB (d : Data G) : Prop where
  K₂_le_L : d.K₂ ≤ d.L
  K₂_le_normalizer : d.K₂ ≤ normalizer (d.A₂ : Set G)
  Λ_le_K₂ : d.Λ ≤ d.K₂
  A₂_irred : ∀ B : Subgroup G, B ≤ d.A₂ → d.K₂ ≤ normalizer (B : Set G) → B = ⊥ ∨ B = d.A₂
  K₂_trans : ∀ k ∈ d.K₂, ∀ k' ∈ d.K₂, k * d.z * k⁻¹ ≠ d.z → k' * d.z * k'⁻¹ ≠ d.z →
    ∃ m ∈ d.K₂, m * d.z = d.z * m ∧ m * (k * d.z * k⁻¹) * m⁻¹ = k' * d.z * k'⁻¹
  A₁_irred : ∀ B : Subgroup G, zpowers d.z ≤ B → B ≤ d.A₁ → d.K₁ ≤ normalizer (B : Set G) →
    B = zpowers d.z ∨ B = d.A₁
  CH_A₁_mod : ∀ n ∈ d.H, n ∈ normalizer (d.A₁ : Set G) →
    (∀ a ∈ d.A₁, n * a * n⁻¹ * a⁻¹ ∈ zpowers d.z) → n ∈ d.withT d.A₁
  w₂_mem_K₁ : d.w₂ ∈ d.K₁
  w₂_mem_K₂ : d.w₂ ∈ d.K₂
  A₁_inf_A₄ : d.A₁ ⊓ d.A₄ ≤ d.X₈ ⊔ zpowers d.z
  A₁_inf_A₂ : d.A₁ ⊓ d.A₂ ≤ (d.X₈ ⊔ zpowers d.z) ⊔ d.conjW (d.X₈ ⊔ zpowers d.z)
  Z₂S_inf : (d.X₈ ⊔ zpowers d.z) ⊓ d.conjW (d.X₈ ⊔ zpowers d.z) ≤ zpowers d.z

end CFSG.EvenSmallLie.UnitarySix.YamadaD
