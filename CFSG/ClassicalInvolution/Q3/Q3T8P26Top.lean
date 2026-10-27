module

public import CFSG.ClassicalInvolution.Q3.Q3T8P26F01
public import CFSG.ClassicalInvolution.Q3.Q3T8P26D03
public import CFSG.ClassicalInvolution.Q3.Q3T8P26E04
public import CFSG.ClassicalInvolution.Q3.Q3T8AFFin

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

section Claim


theorem c26_13_unconditional : C26_13 := by
  have : Fact AlphaFrame3 := ⟨alphaFrame3_proved⟩
  exact c26_13_of_facts (T8YY.layerFrattiniFact_of_center T8ZZ.layerCenterFact_proved)
    (T8YY.pureBCase_of_singleFrame (T8YY.layerFrattiniFact_of_center T8ZZ.layerCenterFact_proved)
      (T8YY.singleFrameFact_of_zero T8ZZ.singleFrameFact0_proved))

end Claim

section Theorem8


theorem thm8A3_proved : Q3.Disc3.Thm8A3 :=
  thm8A3_of_c26_13 c26_13_unconditional

end Theorem8

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
