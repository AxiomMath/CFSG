module

public import CFSG.HardMathSupport.Lang.TwE6Step3.D4LinesFinal

public noncomputable section

namespace CFSG.HardMathSupport.Lang.TwE6Step3

open CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator (PhiPlaneGenAt)


set_option linter.unusedSectionVars false

section Final


theorem twE6SixLines_of_phi6 (h6 : ∀ r, 5 ≤ r → PhiPlaneGenAt (-1) r) : TwE6SixLines :=
  twE6SixLines_of_types linesOfType_A2A2 (linesOfType_D4 h6)

end Final

end CFSG.HardMathSupport.Lang.TwE6Step3
