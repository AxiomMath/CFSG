module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpEvenTypedPSL
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpEvenTypedPSU
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpEvenTypedPSp
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpEvenTypedOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpEvenTypedExc
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpEvenTypedE6
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpEvenTypedSuzRee

public section

namespace CFSG.ComponentClassification.CatFC

theorem evenOuterTypedInput_holds :
    EvenOuterTypedInput :=
  evenOuterTypedInput_of_families fun τ => by
    cases τ
    exacts [evenOuterTypedFamilyInput_PSL, evenOuterTypedFamilyInput_PSU,
      evenOuterTypedFamilyInput_PSp, evenOuterTypedFamilyInput_POmegaOdd,
      evenOuterTypedFamilyInput_POmegaPlus, evenOuterTypedFamilyInput_POmegaMinus,
      evenOuterTypedFamilyInput_G2, evenOuterTypedFamilyInput_F4, evenOuterTypedFamilyInput_E6,
      evenOuterTypedFamilyInput_E7, evenOuterTypedFamilyInput_E8,
      evenOuterTypedFamilyInput_twistedE6, evenOuterTypedFamilyInput_trialityD4,
      evenOuterTypedFamilyInput_twistedB2, evenOuterTypedFamilyInput_twistedG2,
      evenOuterTypedFamilyInput_twistedF4, evenOuterTypedFamilyInput_Tits]

end CFSG.ComponentClassification.CatFC
