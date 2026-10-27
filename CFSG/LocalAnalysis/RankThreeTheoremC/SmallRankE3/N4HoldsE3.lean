module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4Holds
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1E3
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1Holds

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG CFSG.LocalCores CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

section HoldsE3


theorem stepP65OddFive_of_gammaE3 (hγ : N3.GammaStructureP) (hK1 : KFactP65RankThreeS)
    (hK2 : KFactP65RankTwoS) : StepP65OddFive :=
  N1.stepP65OddFive_of_kfactsE3 hK1 hK2
    (kFactP65SingleE3_of_single (kFactSingleW_of_gamma hγ) noTwoComponentsPlane_holds)
    N1.noTwoComponentsE3_holds

theorem stepP65OddSevenU0_of_gammaE3 (hγ : N3.GammaStructureP)
    (hK1 : KFactP65RankThreeS) (hK2 : KFactP65RankTwoS) : StepP65OddSevenU0 :=
  stepP65OddSevenU0_of_kfactsE3 hK1 hK2
    (fun p _ => kFactP65SingleAt_of_single (kFactSingleW_of_gamma hγ) noTwoComponentsPlane_holds p)
    (fun p _ => noTwoComponentsAt_of_plane noTwoComponentsPlane_holds p)

theorem stepP65OddE3U0_of_gammaE3 (hγ : N3.GammaStructureP)
    (hK1 : KFactP65RankThreeS) (hK2 : KFactP65RankTwoS) : StepP65OddE3U0 :=
  stepP65OddE3U0_of_five_seven (stepP65OddFive_of_gammaE3 hγ hK1 hK2)
    (stepP65OddSevenU0_of_gammaE3 hγ hK1 hK2)

theorem stepP65OddE3U0_of_kfactsE3 (hK1 : KFactP65RankThreeS) (hK2 : KFactP65RankTwoS) :
    StepP65OddE3U0 :=
  stepP65OddE3U0_of_gammaE3 N3.gammaStructureP_holds hK1 hK2

theorem slotProp65Five_of_two_kfactsE3 (hK1 : KFactP65RankThreeS) (hK2 : KFactP65RankTwoS) :
    SlotProp65Five :=
  N1.slotProp65Five_of_kfactsE3 hK1 hK2 kFactP65SingleE3_holds N1.noTwoComponentsE3_holds

end HoldsE3

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
