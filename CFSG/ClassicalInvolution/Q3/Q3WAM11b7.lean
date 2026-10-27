module

public import CFSG.ClassicalInvolution.Q3.Q3NMM11
public import CFSG.ClassicalInvolution.Q3.Q3WAM11b3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

theorem m11AutInner_proved : M11AutInner :=
  fun φ => Q3NM.m11_aut_inner φ

end CFSG.ClassicalInvolution.Q3.Q3W
