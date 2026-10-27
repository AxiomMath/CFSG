module

public import CFSG.LargeExtraspecial.S14C13B1c
public import CFSG.LargeExtraspecial.S14C13YMain
public import CFSG.LargeExtraspecial.PSL10Main

public section

namespace CFSG.LargeExtraspecial.S14

open CFSG.LargeExtraspecial.S4

theorem claim14_13B1_of_inputs (hCE : CentralExtInput.{0}) (h2 : PSLPSU10Input) :
    Claim14_13B1 :=
  claim14_13B1_of hCE h2 (ybar13Stmt_of hCE)

theorem claim14_13B1_of_centralExt (hCE : CentralExtInput.{0}) : Claim14_13B1 :=
  claim14_13B1_of_inputs hCE pslpsu10Input

end CFSG.LargeExtraspecial.S14
