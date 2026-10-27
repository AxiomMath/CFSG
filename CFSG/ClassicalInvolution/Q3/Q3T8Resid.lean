module

public import CFSG.ClassicalInvolution.Q3.Q3T8Steps
public import CFSG.ClassicalInvolution.Q3.Q3T8E274B

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected


structure Thm8Residuals3 : Prop where
  c26_2 : C26_2
  c26_13 : C26_13
  c27_4M : C27_4M
  c27_8E4 : C27_8E4
  c27_8nE4 : C27_8nE4

theorem thm8A3_of_residuals (h : Thm8Residuals3) : Q3.Disc3.Thm8A3 :=
  thm8A3_of_thm8A (thm8A_of_c26_2_c26_13 h.c26_2 h.c26_13
    (c27_4a_of_min (c27_2_of_c26_2_c26_13 h.c26_2 h.c26_13) h.c27_4M)
    (c27_8_of_split h.c27_8E4 h.c27_8nE4))

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
