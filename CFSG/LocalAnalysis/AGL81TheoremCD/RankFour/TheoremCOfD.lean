module

public import CFSG.LocalAnalysis.AGL81TheoremCD.FourteenSixteen
public import CFSG.LocalAnalysis.AGL81TheoremCD.RankFour.CStarGenFour

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.RankFour

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem agl81TheoremCFour_of_theoremDFour
    (hD : CFSG.Yardstones.Mf4cdcdf2e013.AGL81TheoremDFour) (h : AGL81FourteenFifteen) :
    CFSG.Yardstones.Mf4cdcdf2e013.AGL81TheoremCFour := by
  intro G _ _ hS hU p M hM hp
  have hC : CStarGen G := cStarGen_of_unique4 hS hU
  have hne : (sigmaSet G M).Nonempty :=
    ⟨p, by rw [sigmaM_eq_uniqueFourSigma hS hU hM]; exact hp⟩
  exact theoremCAt_of_theoremDAt hC hM (h G hC M hM hne) (hD G hS hU p M hM hp)

end CFSG.LocalAnalysis.AGL81TheoremCD.RankFour
