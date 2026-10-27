module

public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpEUp
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpLeafMain
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpSpor
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenOuter
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpA10Main
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddAssemblyHolds
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutMain
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutK3Main

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG

theorem evenAltPumpUp_holds :
    GSThmB.EvenAltPumpUp :=
  evenAltPumpUp_of_inputs
    (evenAltPumpInput_of_leaf
        (evenAltPumpLeaf_of_clauses CatLeafProof.gls3OddLieAutComponentsInput_holds
            CatLeafProof.lieOrderFormulasInput CatLeafProof.evenLieOuterTwoComponentsInput_holds
            (evenAltPumpSporadicClause_of_inputs SolMax.suzOuterComponentsInput_holds
                (SolMax.onOuterComponentsInput_of_local SolMax.ONOut.onOuterLocalInput_holds))))
    (hnPumpInput_of_leaf (hnNotProperFixedLeaf_of_clauses
      CatLeafProof.gls3OddLieAutComponentsInput_holds CatLeafProof.lieOrderFormulasInput
      CatLeafProof.evenLieOuterTwoComponentsInput_holds hnSporadicClause_holds))
    (a10PumpInput_of_leaf (a10PumpLeaf_of_clauses CatLeafProof.gls3OddLieAutComponentsInput_holds
      CatLeafProof.lieOrderFormulasInput CatLeafProof.evenLieOuterTwoComponentsInput_holds))

end CFSG.ComponentClassification.EvenPump
