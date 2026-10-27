module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpTable
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpArmsHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpEvenTypedHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.ResidualA8Proof
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.McLLyInnerCenter

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC


theorem kgPumpTableT_holds : EvenSporadicStandard.HSStd.Zassenhaus.Outer.KGPumpTableT :=
  kgPumpTableT_of_inputs armInputs_holds evenOuterTypedInput_holds heSuzONNoAltEight_proved
    mcl_inner_component_center

end CFSG.ComponentClassification.CatFC
