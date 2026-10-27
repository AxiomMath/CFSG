module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.Reduction
public import CFSG.Milestones.CL_LIT_GH74_sectional_two_rank_four
public import CFSG.RankThree.PartOne.SPOR.Final

public section

namespace CFSG.EvenSporadicStandard.HNRecog.GH73

theorem gh73TheoremA64K_holds :
    GH73TheoremA64K :=
  gh73TheoremA64K_of_models
    (fun G _ _ _ hnonab hrank hsect =>
      CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models G hnonab hrank hsect)
    CFSG.RankThree.PartOne.SPOR.schreierFor_catalog

end CFSG.EvenSporadicStandard.HNRecog.GH73
