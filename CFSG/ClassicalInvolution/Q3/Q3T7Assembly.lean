module

public import CFSG.ClassicalInvolution.Q3.Q3T7Main
public import CFSG.ClassicalInvolution.Q3.Q3T7Wz
public import CFSG.ClassicalInvolution.Q3.Q3T7C231Final
public import CFSG.ClassicalInvolution.Q3.Q3T7P24VFin
public import CFSG.ClassicalInvolution.Q3.Q3T7P25ZFinal
public import CFSG.ClassicalInvolution.Q3.Q3T7MFin

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.Disc3

section Assembly



structure Thm7Residuals3 : Prop where
  s21 : C21_2Three
  s22 : C22_1Three
  s233 : C23_3Three
  qs3 : Q3.QuasisimpleConnected3
  h51 : Q3T7P24.Hyp51TwinInnerThree

theorem Thm7Residuals3.steps (h : Thm7Residuals3) : Thm7Steps3 where
  wz := wz3
  s21 := h.s21
  s22 := h.s22
  s231 := c23_1_proved3
  s233 := h.s233
  s24 := Q3T7P24.c24_1Three_of_thmE' (Q3T8.Asc77.thmE3_of_qs3 h.qs3) h.h51
  s25 := Q3T7P25.c25_E4Three_proved

theorem thm7A3_of_residuals (h : Thm7Residuals3) : Thm7A3 :=
  thm7A3_of_stepsStruct h.steps

end Assembly

end CFSG.ClassicalInvolution.Q3.Q3T7
