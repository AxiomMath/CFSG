module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.LocalAnalysis.AGL81I.Section4

@[expose] def AGL81FourNineteen : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    CFSG.AGLEmbedding.IsClassicalTwoOrG2 (Y ⧸ Subgroup.center Y) →
    ∀ T J : Subgroup (Y ⧸ Subgroup.center Y), CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ →
      Subgroup.normalizer (T : Set (Y ⧸ Subgroup.center Y)) ≤ J →
      J ≠ Subgroup.normalizer (T : Set (Y ⧸ Subgroup.center Y)) → J ≠ ⊤ →
      ∀ d : ℕ, d.Prime → 5 ≤ d → ¬ d ∣ Nat.card J →
        CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 3 →
        CFSG.Open.pRank d (⊤ : Subgroup Y) + 1 ≤ max 2 (CFSG.Open.pRank 3 (⊤ : Subgroup Y))

end CFSG.LocalAnalysis.AGL81I.Section4

end
