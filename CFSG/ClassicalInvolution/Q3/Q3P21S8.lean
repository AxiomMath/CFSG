module

public import CFSG.ClassicalInvolution.Q3.Q3P21S7

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3P21

open CFSG.ClassicalInvolution.Q3.Q3W

section Piece

theorem piece3TwinSU4_of_linear3 (h3 : OddThreeFreeInput) (hW : Q3TW.WeakCT3MinusMap 5)
    (hP : Q3TC.ProductP1Input3) (hL : Q3TY.TwinLinked3) (hlin : TwinSU4Linear3) :
    Piece3TwinSU4 :=
  Q3TY.piece3TwinSU4_of_inputs h3 hW hP hL (twinSU4ShortNode3_of_linear3 h3 hlin)

end Piece

end CFSG.ClassicalInvolution.Q3.Q3P21
