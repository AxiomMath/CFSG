module

public import CFSG.ClassicalInvolution.Q3.Q3TIYNPat
public import CFSG.ClassicalInvolution.Q3.Q3TZRows

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TY


theorem twinYType3On_needed (h3 : OddThreeFreeInput) : TwinYType3On TwinRowNeeded3 :=
  twinYType3On_needed_of_noCentral h3
    (TwinYNoCentral3On.union Q3TZ.twinYNoCentral3_odd3 Q3TZ.twinYNoCentral3_minus4)

theorem piece3TwinB_of_y4_noY2 (h3 : OddThreeFreeInput)
    (hcls : TwinInvolution3) (hP : CommutingProductP1Input3) : Piece3TwinB :=
  piece3TwinB_of_y4On h3 hcls hP (twinYType3On_needed_B (twinYType3On_needed h3))
    (Q3TWY.twinYPatternAtL3_b_all h3)

theorem chainPiece3TwinTD_of_inputs_noY2 (h3 : OddThreeFreeInput) (hcls : TwinInvolution3)
    (hP : CommutingProductP1Input3) : Q3TW.ChainPiece3TwinTD :=
  chainPiece3TwinTD_of_inputsOn h3 hcls hP (twinYType3On_needed_TD (twinYType3On_needed h3))

end CFSG.ClassicalInvolution.Q3.Q3TIY
