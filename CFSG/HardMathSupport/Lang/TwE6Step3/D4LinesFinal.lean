module

public import CFSG.HardMathSupport.Lang.TwE6Step3.D4LinesMain

public noncomputable section

namespace CFSG.HardMathSupport.Lang.TwE6Step3

open CFSG.Open CFSG.LieType.SeitzGeneration
open CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator (PhiPlaneGenAt)

set_option linter.unusedSectionVars false

theorem linesOfType_D4 (h6 : ∀ r, 5 ≤ r → PhiPlaneGenAt (-1) r) : LinesOfType IsD4Kernel :=
  linesOfType_D4_of_ext h6
    (fun _ hq => extSeitzAtInnerFor_trialityD4_even CFSG.Goldschmidt.topStatement hq)

end CFSG.HardMathSupport.Lang.TwE6Step3
