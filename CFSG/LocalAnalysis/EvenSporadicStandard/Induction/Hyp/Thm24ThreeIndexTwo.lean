module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpArmsHolds
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Thm24ThreeIndexTwo.Core
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Thm24ThreeSimple

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open CFSG.EvenSporadicStandard.Solomon78


theorem thm24ThreeUse_holds {s' : TauCeti.SporadicName} (hs' : s' ∈ Sol78Rows) :
    Thm24ThreeUse s' :=
  thm24ThreeUse_of_inputs thm24ThreeSimpleInputs_proved
    CFSG.ComponentClassification.CatFC.armInputs_holds hs'

end CFSG.EvenSporadicStandard.Induction.Hyp
