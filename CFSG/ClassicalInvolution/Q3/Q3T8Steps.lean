module

public import CFSG.ClassicalInvolution.Q3.Q3T8Std8

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

theorem thm8A3_of_thm8A (h : Thm8A) : Q3.Disc3.Thm8A3 :=
  fun G _ _ _ Ω K hs h3 h4 hedge hnt hdisc =>
    h G Ω K (AscStand.of_stand3 hs h3 h4) hedge hnt hdisc

theorem thm8A3_of_steps (h274 : C27_4) (h278 : C27_8) : Q3.Disc3.Thm8A3 :=
  thm8A3_of_thm8A (thm8A_of_steps c27_nbr_proved c27_setup_proved h274 h278)

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
