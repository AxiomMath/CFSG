module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP1Leaf
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP1Spor
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpOddChar
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddAssemblyHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpEvenTypedHolds
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP2

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

theorem chevOddPumpLeaf_holds :
    ChevOddPumpLeaf :=
  chevOddPumpLeaf_of_clauses CatLeafProof.gls3OddLieAutComponentsInput_holds
    CatLeafProof.lieOrderFormulasInput CatFC.evenOuterTypedInput_holds oddLieCharUnique_holds
    chevOddSporadicClause_holds

theorem chevOddCentralPumpInput_holds :
    ChevOddCentralPumpInput :=
  chevOddCentralPumpInput_of_leaf chevOddPumpLeaf_holds

end CFSG.ComponentClassification.GS82PumpInputs
