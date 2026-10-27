module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoSporHe
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoSporMax
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoSporRu

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

theorem threeFourTwoSporadicNone_holds :
    ThreeFourTwoSporadicNone := by
  refine ⟨fun s hs => ?_, threeFourTwoNoneAt_he, threeFourTwoNoneAt_j4⟩
  rcases hs with rfl | rfl
  · exact threeFourTwoNoneAt_mcl
  · exact threeFourTwoNoneAt_ru

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
