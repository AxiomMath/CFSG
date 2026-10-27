module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7ExitGLS3
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7C22H
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7EFin
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7T21D
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7Wz
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7Clique
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8Final
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25Fin
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25N9

public section

namespace CFSG.ClassicalInvolution.Hat2A7R

open CFSG.ClassicalInvolution CFSG.Blueprint

section Final


theorem a7StepJ_of_gh74_tc (hGH : GH74SectionalModels) (hTC : Hat2A7S.A7TC) : A7StepJ :=
  Hat2A7S.a7StepJ_of_branches Hat2A7S.a7T3_proved Hat2A7S.a7T6_proved hTC
      (Hat2A7S.a7T7_of_steps Hat2A7S.a7Wz_proved (Hat2A7S.a7C21_2_of_thmE Hat2A7S.a7ThmE_proved)
          (Hat2A7S.a7C22_1_of_thmE Hat2A7S.a7ThmE_proved) Hat2A7S.a7C23_1_proved
          Hat2A7S.a7C23_3_proved Hat2A7S.a7C24_1_proved
          (Hat2A7S.a7C25_E4_of_noffz Hat2A7S.a7NoFFz_proved
              (Hat2A7S.a7ExitTF4_of_gh74 noNonsolvableClassical_Ly hGH Hat2A7S.a7ExitGLS3_proved)))
      Hat2A7S.a7T8_proved

end Final

end CFSG.ClassicalInvolution.Hat2A7R
