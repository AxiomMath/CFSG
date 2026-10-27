module

public import CFSG.ClassicalInvolution.Q3.Q3T7S23Fin
public import CFSG.ClassicalInvolution.Q3.Q3T7S23H05

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7S23


theorem c23_3Three_of_residuals (hE : Q3T7E.ThmEWithSylow3) (hres : Phan23Residual3) :
    Q3T7.C23_3Three :=
  c23_3Three_of_inputs hE c23_7_proved hres

end CFSG.ClassicalInvolution.Q3.Q3T7S23
