module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerPSp
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4Inner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE8Inner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofTwE6Inner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddTrialityInner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddTriality
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddRee

public section

namespace CFSG.SeitzReduction

open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof


theorem gls3OddLieAutComponentsInput : GLS3OddLieAutComponentsInput :=
  gls3OddLieAutComponentsInput_of_families fun τ => by
    cases τ
    exacts [gls3OddFamilyInput_PSL_holds, gls3OddFamilyInput_PSU_holds,
      gls3OddFamilyInput_PSp_holds,
      gls3OddFamilyInput_POmegaOdd oddOmegaOddLinearInput_holds oddOmegaOddFieldInput_holds,
      gls3OddFamilyInput_POmegaPlus oddOmegaPlusLinearInput_holds oddOmegaPlusFieldInput_holds,
      gls3OddFamilyInput_POmegaMinus oddOmegaMinusLinearInput_holds
        oddOmegaMinusFieldInput_holds,
      gls3OddFamilyInput_G2 oddExcInnerDiagInput_G2,
      gls3OddFamilyInput_F4 oddExcInnerDiagInput_F4,
      gls3OddFamilyInput_E6_holds, gls3OddFamilyInput_E7_holds,
      gls3OddFamilyInput_E8 oddExcInnerDiagInput_E8, gls3OddFamilyInput_twistedE6_holds,
      gls3OddFamilyInput_trialityD4 oddTrialityInnerInput_holds oddTrialityOuterInput_holds,
      gls3OddFamilyInput_twistedB2, gls3OddFamilyInput_twistedG2 oddReeInnerInput_holds,
      gls3OddFamilyInput_twistedF4, gls3OddFamilyInput_Tits]

end CFSG.SeitzReduction
