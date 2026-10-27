module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma45

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def FooteThm47Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), FooteSec4 G L →
    ∀ M : Subgroup G, IsFooteM L M → ∀ t : G, orderOf t = 2 → t ∈ coreActionKernel M →
      3 ≤ CFSG.pRank 2 ↥(coreActionKernel M ⊓ centralizer ({t} : Set G))

end CFSG.ComponentClassification.FooteLit
