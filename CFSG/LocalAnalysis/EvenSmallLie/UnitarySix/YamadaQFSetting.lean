module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDSetting

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup

variable {G : Type*} [Group G]

structure HypF (d : Data G) (φ : G) : Prop where
  φ_comm_t : φ * d.t = d.t * φ
  φ_comm_e : φ * d.e = d.e * φ
  φ_norm_A₄ : φ ∈ normalizer (d.A₄ : Set G)
  φ_u₁ : φ * d.u₁ * φ⁻¹ = d.u₁
  φ_u₂ : φ * d.u₂ * φ⁻¹ = d.u₁ * d.u₂
  φ_a₀ : φ * d.a₀ * φ⁻¹ = d.a₀
  φ_sq : φ * φ = 1 ∨ φ * φ = d.t
  φ_not_mem : φ ∉ d.L ⊔ zpowers d.t
  card_le : ∀ P : Subgroup G,
    P ≤ d.H ⊓ centralizer ({d.e} : Set G) ⊓ normalizer (d.A₄ : Set G) →
    IsPGroup 2 P → Nat.card P ≤ 2 ^ 8

end CFSG.EvenSmallLie.UnitarySix.YamadaD
