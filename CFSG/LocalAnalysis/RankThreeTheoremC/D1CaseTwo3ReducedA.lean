module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

section Reduced

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {Rb : Sylow p Y} {Y₀ : Subgroup Y}

theorem _root_.CFSG.AGLEmbedding.ReducedNongeneration.isCaseTwoGroup_of_not_le3
    (h : ReducedNongeneration p Y Rb Y₀)
    (hX : CatalogSimpleSections Y) (hOut : KFactOutCyclic) (hS : KFactSeitzCyc)
    (hcyc : ∀ L : Subgroup Y, IsComponentOf L ⊤ → IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    (h3 : Open.pRank p (Rb : Subgroup Y) = 3) {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hLY₀ : ¬ L ≤ Y₀) : IsCaseTwoGroup p L :=
  h.isCaseTwoGroup_of_not_le_of_aut hX (h.cycAutRankLeTwo_of_kFactOutCyclic hX hOut) hS hcyc h3 hL
    hLY₀

end Reduced

end CFSG.LocalAnalysis.RankThreeTheoremC
