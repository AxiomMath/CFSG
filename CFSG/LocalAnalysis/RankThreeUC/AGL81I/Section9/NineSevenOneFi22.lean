module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineSevenOne
import CFSG.HardMathSupport.Solomon.Coordinator.I10_21Fi22
import CFSG.HardMathSupport.Solomon.Coordinator.I10_21Fi22Two
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

theorem kFactFi22ThreeRank_holds :
    KFactFi22ThreeRank := by
  intro X F _ _ _ hF φ hφ
  obtain ⟨e⟩ := hF
  haveI : Finite F := Finite.of_surjective φ hφ
  obtain ⟨V, hV, hVc⟩ := CFSG.HardMathSupport.Solomon.Coordinator.i1021_fi22_two_rank_five e
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
  exact CFSG.HardMathSupport.Solomon.Coordinator.i1021_fi22_of_two_rank e hV hVc X φ hφ

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
