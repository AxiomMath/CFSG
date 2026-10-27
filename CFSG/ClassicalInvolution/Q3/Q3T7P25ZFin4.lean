module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25ZFin3
public import CFSG.ClassicalInvolution.Q3.Q3T7P25YMFinB

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7P25

theorem c25_E4Three_of_parity (hP : ParityE4Three) : Q3T7.C25_E4Three :=
  c25_E4Three_of_three_residuals hP modelFacts3_proved m8gFacts3_proved

end CFSG.ClassicalInvolution.Q3.Q3T7P25
