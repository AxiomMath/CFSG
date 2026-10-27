module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10THolds
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpA8Lift
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpA8Leaf
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpA8Spor
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddAssemblyHolds
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpLeafMain
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpSpor
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TR18HS
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TR18L44

public section

namespace CFSG.ComponentClassification.GSThmB.A10T

theorem gs82R18Input_holds :
    GS82R18Input := by
  intro S _ _ hS h
  rcases h with hL | hH
  · exact ⟨outerNotSylowCentral_l44 hS hL, fixedA8KernelTrivial_l44 hS hL⟩
  · obtain ⟨e⟩ := hH
    exact ⟨outerNotSylowCentral_hs e, fixedA8KernelTrivial_hs e⟩

theorem gs82CentXA10TransferStatementK_holds :
    GS82CentXA10TransferStatementK :=
  gs82CentXA10TransferStatementK_of_inputs
      (EvenPump.evenAltPumpInput_of_leaf
          (EvenPump.evenAltPumpLeaf_of_clauses CatLeafProof.gls3OddLieAutComponentsInput_holds
              CatLeafProof.lieOrderFormulasInput CatLeafProof.evenLieOuterTwoComponentsInput_holds
              (EvenPump.evenAltPumpSporadicClause_of_inputs SolMax.suzOuterComponentsInput_holds
                  (SolMax.onOuterComponentsInput_of_local SolMax.ONOut.onOuterLocalInput_holds))))
      (EvenPump.hnPumpInput_of_leaf
          (EvenPump.hnNotProperFixedLeaf_of_clauses CatLeafProof.gls3OddLieAutComponentsInput_holds
              CatLeafProof.lieOrderFormulasInput CatLeafProof.evenLieOuterTwoComponentsInput_holds
              EvenPump.hnSporadicClause_holds))
      (EvenPump.a8PumpInput_of_leaf
          (EvenPump.a8PumpLeaf_of_clauses CatLeafProof.gls3OddLieAutComponentsInput_holds
              CatLeafProof.lieOrderFormulasInput CatFC.evenOuterTypedInput_holds
              EvenPump.a8SporadicClause_holds)) hnFixedComponents_holds hnInnerFixedComponents_holds
      hnOuterIndex_holds gs82R18Input_holds

end CFSG.ComponentClassification.GSThmB.A10T
