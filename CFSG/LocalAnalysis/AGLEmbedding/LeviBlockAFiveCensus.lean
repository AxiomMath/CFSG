module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockAFiveLin
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockAFiveSymp
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockAFiveUni
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockAFiveOrthPlus
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockAFiveOrthMinus
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockAFiveGTwo
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockAFiveSmall
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockAFiveGeneric
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubCenter

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem kFactCompParabTwoFives_of_griess
    (hGA : GriessAllModelsStatement) :
    KFactCompParabTwoFives := by
  have hZ : OddCenterRest := oddCenterRest_of_griess hGA
  have hLB := leviBlocksOfFiveComponents_holds
  exact kFactCompParabTwoFives_of_families (kFactCompParabTwoFivesOn_linear hLB hGA)
    (kFactCompParabTwoFivesOn_twistedA hLB) (kFactCompParabTwoFivesOn_idxB hLB hZ)
    (kFactCompParabTwoFivesOn_idxD hZ hLB) (kFactCompParabTwoFivesOn_twistedD hLB hZ)
    (kFactCompParabTwoFivesOn_g2 hLB hGA) (kFactCompParabTwoFivesOn_small hZ hLB)

theorem kFactCompParabOneFive_of_griess
    (hGA : GriessAllModelsStatement) :
    KFactCompParabOneFive := by
  have hZ : OddCenterRest := oddCenterRest_of_griess hGA
  have hLB := leviBlocksOfFiveComponents_holds
  exact kFactCompParabOneFive_of_families (kFactCompParabOneFiveOn_linear hLB hGA)
    (kFactCompParabOneFiveOn_twistedA hLB) (kFactCompParabOneFiveOn_idxB hLB hZ)
    (kFactCompParabOneFiveOn_idxD hZ hLB) (kFactCompParabOneFiveOn_twistedD hZ)
    (kFactCompParabOneFiveOn_g2 hLB hGA) (kFactCompParabOneFiveOn_small hZ hLB)

end CFSG.AGLEmbedding
