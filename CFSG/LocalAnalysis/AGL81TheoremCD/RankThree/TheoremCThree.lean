module

public import CFSG.LocalAnalysis.AGL81TheoremCD.FourteenSixteen
public import CFSG.LocalAnalysis.AGL81TheoremCD.RankThree.CStarGenThree

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.RankThree

theorem agl81TheoremC_of_fourteenFifteen (h1415 : AGL81FourteenFifteen) {G : Type} [Group G]
    [Finite G] (hS : CFSG.LocalAnalysis.RankThreeUC.Standing G)
    (hD : CFSG.LocalAnalysis.RankThreeUC.AGL81TheoremD G) :
    CFSG.LocalAnalysis.RankThreeUC.AGL81TheoremC G := by
  intro hUC p hp P M hw
  have hC : CStarGen G := cStarGen_of_rankThreeUC hS hUC
  have hσ : (sigmaSet G M).Nonempty :=
    ⟨p, hp, by rw [(hw.pRank_eq_three hS hp).2]; omega⟩
  exact theoremCAt_of_theoremDAt hC hw.maxLocal (h1415 G hC M hw.maxLocal hσ)
    (hD hUC p hp P M hw)

end CFSG.LocalAnalysis.AGL81TheoremCD.RankThree
