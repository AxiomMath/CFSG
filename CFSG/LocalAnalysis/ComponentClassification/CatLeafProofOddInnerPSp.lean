module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSp

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG.ComponentClassification.CatLeaf

theorem oddPSpInnerDiagInput : OddPSpInnerDiagInput := by
  intro r K _ _ p f hp hp2 hK hadm A hA L hL
  exact oddLie_inner_psp hp hp2 hK hadm A hA hL

theorem gls3OddFamilyInput_PSp_holds : GLS3OddFamilyInput .PSp :=
  gls3OddFamilyInput_PSp oddPSpInnerDiagInput

end CFSG.ComponentClassification.CatLeafProof
