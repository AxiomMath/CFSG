module

public import CFSG.ClassicalInvolution.Q3.Q3TZMax

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TZ

open CFSG.Open hiding StatedLieTag StatedLieAdmissible


theorem twinYNoCentral3_odd3 : Q3TIY.TwinYNoCentral3On fun t n => t = .POmegaOdd ∧ n = 3 :=
  twinYNoCentral3_of_twinPairMax3 fun _ _ _ hl => by
    obtain ⟨rfl, rfl⟩ := hl
    exact twinPairMax3_odd3

theorem twinYNoCentral3_minus4 : Q3TIY.TwinYNoCentral3On fun t n => t = .POmegaMinus ∧ n = 4 :=
  twinYNoCentral3_of_twinPairMax3 fun _ _ _ hl => by
    obtain ⟨rfl, rfl⟩ := hl
    exact twinPairMax3_minus4

end CFSG.ClassicalInvolution.Q3.Q3TZ
