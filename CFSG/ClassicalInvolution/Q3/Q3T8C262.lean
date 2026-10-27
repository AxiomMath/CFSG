module

public import CFSG.ClassicalInvolution.Q3.Q3T8C262Act
public import CFSG.ClassicalInvolution.Q3.Q3T8C262B
public import CFSG.ClassicalInvolution.Q3.Q3T8Resid

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

theorem c26_2_proved : C26_2 :=
  c26_2_of_x s26XProper_proved (s26XEdgeless_of_muZ2 l7_5_2_proved s26XMuZ2_proved)
    (s26XTop_of_c26_1 T8R.c26_1) s26XMuZ2_proved

theorem thm8Residuals3_of_rest (h13 : C26_13) (h4M : C27_4M) (h8E : C27_8E4)
    (h8n : C27_8nE4) : Thm8Residuals3 :=
  ⟨c26_2_proved, h13, h4M, h8E, h8n⟩

theorem thm8A3_of_rest (h13 : C26_13) (h4M : C27_4M) (h8E : C27_8E4) (h8n : C27_8nE4) :
    Q3.Disc3.Thm8A3 :=
  thm8A3_of_residuals (thm8Residuals3_of_rest h13 h4M h8E h8n)

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
