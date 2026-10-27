module

public import CFSG.ClassicalInvolution.Q3.Q3T7S23D04
public import CFSG.ClassicalInvolution.Q3.Q3T7S23E02

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7S23


theorem phan23Residual3_of_oddCore
    (hO : OddCoreLayer23Neg3) (hSp : OddCoreLayer23Sp3) (hPlus : OddCoreLayer23Plus3) :
    Phan23Residual3 :=
  phan23Residual3_of_chains (b3Chain23_of_yside hO hSp) (d4Chain23_of_oddCore hO hPlus)

end CFSG.ClassicalInvolution.Q3.Q3T7S23
