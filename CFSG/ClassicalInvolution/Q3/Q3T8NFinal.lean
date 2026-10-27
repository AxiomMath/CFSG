module

public import CFSG.ClassicalInvolution.Q3.Q3T8NAssem
public import CFSG.ClassicalInvolution.Q3.Q3T8E4NRB
public import CFSG.ClassicalInvolution.Q3.Q3T8C262
public import CFSG.ClassicalInvolution.Q3.Q3T8C274
public import CFSG.ClassicalInvolution.Q3.Q3T8C278E4
public import CFSG.ClassicalInvolution.Q3.Q3T8Hyp51

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

theorem c27_8nE4_of_inputs (h13 : C26_13) (hα : AlphaFrame3) : C27_8nE4 := by
  have h2 : C27_2 := c27_2_of_c26_2_c26_13 c26_2_proved h13
  have h4a : C27_4a := c27_4a_of_min h2 c27_4M_proved
  have h4 : C27_4 := c27_4_of_steps h2 h4a
  exact c27_8nE4_of_YnE4 (c27_YnE4_of_core3 h2 (c27_Oab3_of_inputs hα hyp51Tri_proved h2 h4)
    (T8V.c27_Ysmall_of_e4sec e4SecNoRoot3))

theorem thm8A3_of_inputs (h13 : C26_13) (hα : AlphaFrame3) : Q3.Disc3.Thm8A3 :=
  thm8A3_of_rest h13 c27_4M_proved c27_8E4_proved (c27_8nE4_of_inputs h13 hα)

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
