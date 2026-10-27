module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCent
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubPrime
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusRadical
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinThreeMain
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinPrime
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusTwistedA
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeG2
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.FixPrimeCycB
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbedding


theorem kFactFixCensusCenter_holds (hGA : CFSG.Open.GriessAllModelsStatement) :
    KFactFixCensusCenter :=
  kFactFixCensusCenter_of_families (fixCensusCenterA hGA) fixCensusCenterVoid_isLieOf_twistedA
    (oddCenterRest_of_griess hGA)

section Glue


theorem kFactFixCensusThree_of_rest (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSch : KFactCatalogSchreier)
    (hB : FixThreeVoid (IsLieOf IdxBResidual)) (hD : FixThreeVoid (IsLieOf IdxDResidual))
    (h2D : FixThreeVoid (IsLieOf IdxTwistedDResidual)) (hS : FixThreeVoid IsSmallTwoOrG2) :
    KFactFixCensusThree :=
  kFactFixCensusThree_of_reduced (glueVhyp_of_schreier hSch) (fixThreeA hGA)
    fixThreeVoid_isLieOf_twistedA (fixThreeVoid_b_of_residual hB) (fixThreeVoid_d_of_residual hD)
    (fixThreeVoid_twistedD_of_residual h2D) fixThreeVoid_g2 hS

theorem kFactFixCensusPrime_of_rest (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSch : KFactCatalogSchreier)
    (hD : FixPrimeCycTorus IdxD) (h2D : FixPrimeCycTorus IdxTwistedD) : KFactFixCensusPrime :=
  kFactFixCensusPrime_of_reduced (glueVhyp_of_schreier hSch) (fixPrimeA hGA)
    (fixPrimeTwistedA_of_griess hGA)
    (fixPrimeCyc_of_halves (fixPrimeCycTorusFree_b hGA)
      CFSG.HardMathSupport.Curtis.NaturalModuleCensus.fixPrimeCycTorus_b)
    (fixPrimeCyc_of_halves (fixPrimeCycTorusFree_d hGA) hD)
    (fixPrimeCyc_of_halves (fixPrimeCycTorusFree_twistedD hGA) h2D) fixPrimeCyc_g2
    (fixPrimeCyc_small hGA) (oddCenterRest_of_griess hGA)

end Glue

end CFSG.AGLEmbedding
