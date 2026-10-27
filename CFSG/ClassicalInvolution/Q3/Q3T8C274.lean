module

public import CFSG.ClassicalInvolution.Q3.Q3T8L274B

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

theorem c27_4M_proved : C27_4M := by
  intro G _ _ _ Ω K J S R T W z t hs _ S₂ hRS₂ hcount x _ hx2 hx1 hcent
  exact Layer.centralizer_le_H274_of_eight3 hs hRS₂ hcount hx2 hx1 hcent

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
