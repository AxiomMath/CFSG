module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSU
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddTwisted
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSL
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSp

public section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

theorem gls3OddLieAutComponentsInput_of_inputs
    (hPSLi : OddPSLInnerDiagInput) (hPSLg : OddPSLGraphInput)
    (hPSUi : OddPSUInnerDiagInput) (hPSUg : OddPSUGraphInput)
    (hPSpi : OddPSpInnerDiagInput)
    (hOOl : OddOmegaOddLinearInput) (hOOf : OddOmegaOddFieldInput)
    (hOPl : OddOmegaPlusLinearInput) (hOPf : OddOmegaPlusFieldInput)
    (hOMl : OddOmegaMinusLinearInput) (hOMf : OddOmegaMinusFieldInput)
    (hG2 : OddExcInnerDiagInput .G2) (hF4 : OddExcInnerDiagInput .F4)
    (hE6 : OddExcInnerDiagInput .E6) (hE6g : OddE6GraphInput)
    (hE7 : OddExcInnerDiagInput .E7) (hE8 : OddExcInnerDiagInput .E8)
    (h2E6i : OddTwistedE6InnerInput) (h2E6o : OddTwistedE6OuterInput)
    (h3D4i : OddTrialityInnerInput) (h3D4o : OddTrialityOuterInput)
    (h2G2 : OddReeInnerInput) :
    GLS3OddLieAutComponentsInput :=
  gls3OddLieAutComponentsInput_of_families fun τ => by
    cases τ
    exacts [gls3OddFamilyInput_PSL hPSLi hPSLg, gls3OddFamilyInput_PSU hPSUi hPSUg,
      gls3OddFamilyInput_PSp hPSpi, gls3OddFamilyInput_POmegaOdd hOOl hOOf,
      gls3OddFamilyInput_POmegaPlus hOPl hOPf, gls3OddFamilyInput_POmegaMinus hOMl hOMf,
      gls3OddFamilyInput_G2 hG2, gls3OddFamilyInput_F4 hF4, gls3OddFamilyInput_E6 hE6 hE6g,
      gls3OddFamilyInput_E7 hE7, gls3OddFamilyInput_E8 hE8,
      gls3OddFamilyInput_twistedE6 h2E6i h2E6o, gls3OddFamilyInput_trialityD4 h3D4i h3D4o,
      gls3OddFamilyInput_twistedB2, gls3OddFamilyInput_twistedG2 h2G2,
      gls3OddFamilyInput_twistedF4, gls3OddFamilyInput_Tits]

end CFSG.ComponentClassification.CatLeafProof
