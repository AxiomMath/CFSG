module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLMain
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpClause1
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpArmsHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpEvenTypedHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.ResidualA8Proof
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.McLLyInnerCenter

public section

set_option linter.unusedSectionVars false

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open CFSG.ComponentClassification.CatFC


theorem fixedA8Lookup_holds : FixedA8Lookup := by
  intro S _ _ _ hna hcat σ hσ D hD hA8
  exact clause1_of_inputs armInputs_holds evenOuterTypedInput_holds heSuzONNoAltEight_proved
    mcl_inner_component_center hna hcat hσ hD hA8

theorem nonExactShapeEightLookup_holds : NonExactShapeEightLookup :=
  nonExactShapeEightLookup_of_fixedA8Lookup fixedA8Lookup_holds

end CFSG.OddStandard.AltStdSec.SwapPartner
