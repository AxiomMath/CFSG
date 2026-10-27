module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25ZFin
public import CFSG.ClassicalInvolution.Q3.Q3T7P25NC4

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7P25



theorem c25_E4Three_of_three_residuals (hP : ParityE4Three) (hM : ModelFacts3) (hM8 : M8GFacts3) :
    Q3T7.C25_E4Three :=
  c25_E4Three_of_four_residuals nc4Fact3_proved hP hM hM8

end CFSG.ClassicalInvolution.Q3.Q3T7P25
