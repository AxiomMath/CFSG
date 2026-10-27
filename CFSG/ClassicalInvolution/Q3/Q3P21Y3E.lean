module

public import CFSG.ClassicalInvolution.Q3.Q3P21Y3D
public import CFSG.ClassicalInvolution.Q3.Q3P21Y3A
public import CFSG.ClassicalInvolution.Q3.Q3P21Y3B
public import CFSG.ClassicalInvolution.Q3.Q3P21Y1A
public import CFSG.ClassicalInvolution.Q3.Q3P21Y1B
public import CFSG.ClassicalInvolution.Q3.Q3P21Y1C
public import CFSG.ClassicalInvolution.Q3.Q3P21S8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3P21

open CFSG.ClassicalInvolution.Q3.Q3W

theorem twinSU4Linear3_proved (h3 : OddThreeFreeInput) (hP : Q3TC.ProductP1Input3) :
    TwinSU4Linear3 :=
  twinSU4Linear3_of_inputs h3 hP y1c y1a y1b (fun c => liftY c) (fun c => stab_psu4 c)

theorem piece3TwinSU4_proved (h3 : OddThreeFreeInput) (hW : Q3TW.WeakCT3MinusMap 5)
    (hP : Q3TC.ProductP1Input3) (hL : Q3TY.TwinLinked3) : Piece3TwinSU4 :=
  piece3TwinSU4_of_linear3 h3 hW hP hL (twinSU4Linear3_proved h3 hP)

end CFSG.ClassicalInvolution.Q3.Q3P21
