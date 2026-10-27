module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDSetting

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup

variable {G : Type*} [Group G]

structure HypC (d : Data G) : Prop where
  A₁_sq : ∀ a ∈ d.A₁, a * a ∈ zpowers d.z
  hom_wedge_A₁ : ∀ β : G → G → G, (∀ a ∈ d.A₁, ∀ b ∈ d.A₁, β a b ∈ d.A₁) →
    (∀ a ∈ d.A₁, ∀ a' ∈ d.A₁, ∀ b ∈ d.A₁,
      (β a b * β a' b)⁻¹ * β (a * a') b ∈ zpowers d.z) →
    (∀ a ∈ d.A₁, ∀ b ∈ d.A₁, ∀ b' ∈ d.A₁,
      (β a b * β a b')⁻¹ * β a (b * b') ∈ zpowers d.z) →
    (∀ a ∈ d.A₁, β a a ∈ zpowers d.z) →
    (∀ b ∈ d.A₁, β d.z b ∈ zpowers d.z) →
    (∀ k ∈ d.K₁, ∀ a ∈ d.A₁, ∀ b ∈ d.A₁,
      (k * β a b * k⁻¹)⁻¹ * β (k * a * k⁻¹) (k * b * k⁻¹) ∈ zpowers d.z) →
    ∀ a ∈ d.A₁, ∀ b ∈ d.A₁, β a b ∈ zpowers d.z

end CFSG.EvenSmallLie.UnitarySix.YamadaD
