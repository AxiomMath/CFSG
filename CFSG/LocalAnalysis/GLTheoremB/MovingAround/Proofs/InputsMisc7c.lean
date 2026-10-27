module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsMisc7b

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7c

@[expose] def Input7_10_1Rest : Prop :=
  InputsMisc7.ResOddE6 ∧ InputsMisc7.ResOddTwE6 ∧ InputsMisc7.ResOddD4 ∧ InputsMisc7.ResOddTrivialLie

section Holds

set_option linter.unusedSectionVars false


theorem input7_10_1_of_rest (h : Input7_10_1Rest) : Input185.Input7_10_1 :=
  InputsMisc7.input7_10_1_of_exceptional h.1 h.2.1 h.2.2.1 h.2.2.2

end Holds

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7c

end
