module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8Four

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

section Final


theorem a7T8_proved : A7T8 :=
  a7T8_of_steps a7C27_nbr_proved a7C27_setup_proved a7C27_4_proved
    (Hat2A7S8.a7C27_8_of_steps a7C26_1_proved a7C27_4_proved)

end Final

end CFSG.ClassicalInvolution.Hat2A7S
