module

public import CFSG.LocalAnalysis.ABGTheoremB.V3Defs

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

structure R1NFacts (J : Subgroup G) : Prop where
  normalizes : ∀ W ∈ σ.familyW J, ∀ X : Subgroup G, X ≤ σ.N → IsPGroup σ.p X →
    σ.D ≤ Subgroup.normalizer (X : Set G) →
      X ≤ Subgroup.normalizer ((W ⊔ σ.ON : Subgroup G) : Set G)
  centralizer : ∀ W ∈ σ.familyW J, ∀ X : Subgroup G, X ≤ σ.N → IsPGroup σ.p X →
    σ.D ≤ Subgroup.normalizer (X : Set G) → ∀ y ∈ X,
      (∀ w ∈ W, y * w * y⁻¹ * w⁻¹ ∈ σ.ON) → y ∈ σ.ON
  generates : ∀ W ∈ σ.familyW J, ∀ X : Subgroup G, X ≤ σ.N → IsPGroup σ.p X →
    σ.D ≤ Subgroup.normalizer (X : Set G) → ∀ M : Subgroup G, σ.L ≤ M → M ≤ σ.N →
      M ≤ W ⊔ σ.D ⊔ (M ⊓ Subgroup.normalizer ((σ.ON ⊔ X : Subgroup G) : Set G)) ⊔ σ.ON

end Setting

end CFSG.ABGTheoremB
