module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieMain
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieModel
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieInputs
public import CFSG.LieType.HighestRoot.ModelCenter
public import CFSG.LieType.HighestRoot.ModelAutLift
public import CFSG.LieType.HighestRoot.SL2Outer
public import CFSG.LieType.HighestRoot.CentTrialitySL2
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma34
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec3Config

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open CFSG.ComponentClassification.AS76b

theorem modelHighestRootData : ModelHighestRootData :=
  modelHighestRootData_of oddLieInputs modelCenterPPrime modelAutLift sl2OuterComm
    CFSG.LieType.HighestRoot.trialityD4SL2Unique

theorem rankTwoOddLieStandard_of_foundation (hT2 : Asc76Theorem2) (h4 : Asc75Theorem4) :
    RankTwoStandard.RankTwoOddLieStandard :=
  rankTwoOddLieStandard_of oddLieInputs modelHighestRootData
    (section3Config_of_asc76Theorem2 hT2 h4 asc08Lemma34) (lemma32_of_asc76Theorem2 hT2)

end CFSG.ComponentClassification.RankTwoOddLie
