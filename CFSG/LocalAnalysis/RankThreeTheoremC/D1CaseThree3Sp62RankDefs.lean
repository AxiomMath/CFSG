module

public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorBlocks

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

@[expose] def KFactU62ThreeRank : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (d : TauCeti.ValidLieTypeIndex), IsUSixTwoIndex d →
    Nonempty (Y ≃* CatGroup d) → 4 ≤ Open.pRank 3 (⊤ : Subgroup Y)

@[expose] def KFactOmegaMinusThreeRank : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (m : ℕ) (d : TauCeti.ValidLieTypeIndex), 5 ≤ m →
    IsOmegaMinusTwoIndex m d → Nonempty (Y ≃* CatGroup d) → 4 ≤ Open.pRank 3 (⊤ : Subgroup Y)

end CFSG.LocalAnalysis.RankThreeTheoremC
