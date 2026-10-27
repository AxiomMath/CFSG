module

public import CFSG.HardMathSupport.Solomon.Coordinator.PumpingUpProgress
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddTop
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcChar3
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.D4Outer

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

set_option linter.unusedSectionVars false

theorem pumpingUpFacts_of_exc_residuals
    (h33 : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.Input14_33TypeSameField)
    (hBM : NoOrderSixtyFiveBM) (hR : ∀ name ∈ restNamesOpen, SporNoPumpup name)
    (hD4 : LieComp.D4OuterExport) (hres : LieComp.ExcRationalLieTypes)
    (hout : LieComp.TrialityOuterExport) (hO3 : LieComp.ExcChar3OuterExport)
    (hExc5 : LieComp.LieCompsOn 5 .exceptional) :
    CFSG.Yardstones.M67c2c3e09a6b.PumpingUpFacts :=
  pumpingUpFacts_of_residuals h33 hBM hR YS08.LieQ.lieQConstrainedInner_three_holds
    (YS08.LieQ.lieQConstrainedInner_of_ne_three Nat.prime_five (by norm_num) (by norm_num)) hD4 hres
    hout (LieComp.excChar3Export_of_outer YS08.LieQ.lieQConstrainedInner_three_holds hO3) hExc5

theorem pumpingUpFacts_of_open_residuals
    (h33 : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.Input14_33TypeSameField)
    (hBM : NoOrderSixtyFiveBM) (hR : ∀ name ∈ restNamesOpen, SporNoPumpup name)
    (hres : LieComp.ExcRationalLieTypes) (hodd : LieComp.TrialityOddA2Comps)
    (hD43 : LieComp.D4Char3Outer) (hO3 : LieComp.ExcChar3OuterExport)
    (hExc5 : LieComp.LieCompsOn 5 .exceptional) :
    CFSG.Yardstones.M67c2c3e09a6b.PumpingUpFacts :=
  pumpingUpFacts_of_exc_residuals h33 hBM hR (LieComp.d4OuterExport_of hodd hD43) hres
    (LieComp.trialityOuterExport_of hodd) hO3 hExc5

end CFSG.HardMathSupport.Solomon.Coordinator
