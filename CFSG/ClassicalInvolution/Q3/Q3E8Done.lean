module

public import CFSG.ClassicalInvolution.Q3.Q3E8Final
public import CFSG.ClassicalInvolution.Q3.Q3E8TorCore

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

set_option linter.unusedSectionVars false


theorem piece3E8_of_odd3_product (h3 : OddThreeFreeInput) (hP1x : Q3TC.ProductP1Input3) :
    Piece3E8 :=
  piece3E8_of_inputs h3 hP1x toralStdE73

end CFSG.ClassicalInvolution.Q3.Q3W
