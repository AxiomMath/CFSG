module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerULift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSU

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG.ComponentClassification.CatLeaf

theorem oddPSUInnerDiagInput : OddPSUInnerDiagInput := by
  intro n K _ p f h hp2 hadm A hA L hL
  exact oddLie_inner_psu h hp2 hadm A hA hL

theorem gls3OddFamilyInput_PSU_of_graphInput (hgraph : OddPSUGraphInput) :
    GLS3OddFamilyInput .PSU :=
  gls3OddFamilyInput_PSU oddPSUInnerDiagInput hgraph

end CFSG.ComponentClassification.CatLeafProof
