module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25Mix
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25Six

public section

namespace CFSG.ClassicalInvolution.Hat2A7S

section Fin



theorem a7C25_E4_of_16inv (hinv : A7C25_16inv) (hexit : A7ExitTF4) : A7C25_E4 :=
  a7C25_E4_of_6_16inv a7C25_6_proved hinv hexit

theorem a7C25_E4_of_mix_noffz (hmix : A7Mix25) (hno : A7NoFFz) (hexit : A7ExitTF4) :
    A7C25_E4 :=
  a7C25_E4_of_16inv
    (a7C25_16inv_of_noffz (a7C25_11_of_5_6 a7C25_5_proved a7C25_6_proved) hmix hno) hexit

theorem a7C25_E4_of_noffz (hno : A7NoFFz) (hexit : A7ExitTF4) : A7C25_E4 :=
  a7C25_E4_of_mix_noffz a7Mix25_proved hno hexit

end Fin

end CFSG.ClassicalInvolution.Hat2A7S
