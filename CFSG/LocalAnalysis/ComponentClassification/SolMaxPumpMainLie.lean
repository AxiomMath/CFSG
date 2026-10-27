module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpSpor
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpLeafMain
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenOuter

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG CFSG.ComponentClassification.CatLeaf

theorem alternatingPumpUpInput_of_gls3
    (hGLS : GLS3OddLieAutComponentsInput) (hSuz : SuzOuterComponentsInput)
    (hON : ONOuterComponentsInput) : Sol78.AlternatingPumpUpInput :=
  alternatingPumpUpInput_of_leaf
      (altPumpLeaf_of_clauses hGLS CatLeafProof.lieOrderFormulasInput
          CatLeafProof.evenLieOuterTwoComponentsInput_holds
          (altPumpSporadicClause_of_inputs hSuz hON))

end CFSG.ComponentClassification.SolMax
