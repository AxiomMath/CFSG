module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma45

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def FooteLemma410Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), FooteSec4 G L →
    (Nonempty (L ⧸ Open.fusionZStar L ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ^ f = 9 ∧ Blueprint.LieModel (L ⧸ Open.fusionZStar L) .PSL 2 p f) →
    ∀ M : Subgroup G, IsFooteM L M → ∀ g : G, ∀ E : Subgroup G,
      E ≤ coreActionKernel (conjugate M g) ⊓ normalizer (M : Set G) →
      (∀ x ∈ E, x ^ 2 = 1) → Nat.card E = 8 →
      (∃ x ∈ coreActionKernel M ⊓ coreActionKernel (conjugate M g), orderOf x = 2) ∨
        M ≤ normalizer (conjugate M g : Set G)

end CFSG.ComponentClassification.FooteLit
