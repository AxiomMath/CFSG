module

public import CFSG.LocalAnalysis.ABGTheoremB.Setting

public section

namespace CFSG.ABGTheoremB.TotallyInverted

open CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def ABG_IV_6_2 (σ : Setting G) (r : ℕ) : Prop :=
  ∀ H ∈ σ.familyL r, ∀ R₁ : Subgroup G, R₁ ≠ ⊥ → IsPGroup r R₁ → R₁ ≤ oddCoreIn H →
    σ.D ≤ Subgroup.normalizer (R₁ : Set G) →
    (H : Set G) ⊆ (Subgroup.normalizer (R₁ : Set G) : Set G) * (oddCoreIn H : Set G) →
    (∃ R₀ : Subgroup G, IsSylowOf r R₀ (oddCoreIn H) ∧
      R₀ ≤ Subgroup.normalizer (R₁ : Set G)) →
    Subgroup.normalizer (R₁ : Set G) ∈ σ.familyL r

end CFSG.ABGTheoremB.TotallyInverted
