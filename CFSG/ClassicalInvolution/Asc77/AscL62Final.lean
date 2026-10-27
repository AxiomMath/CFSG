module

public import CFSG.ClassicalInvolution.Asc77.AscL62C66b
public import CFSG.ClassicalInvolution.Asc77.AscSix67
public import CFSG.ClassicalInvolution.Asc77.AscL62Main

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]

theorem l6_6ii_proved : L6_6ii p f :=
  l6_6ii_of_core66 p f fun hp hq _ _ _ _ hΩ => AscL62.core66 hp hq hΩ

theorem l6_6iiAEmpty_proved : L6_6iiAEmpty p f :=
  l6_6iiAEmpty_of_l6_6ii p f (l6_6ii_proved p f)

theorem l6_6_proved : L6_6 p f :=
  l6_6_of_i_ii p f (l6_6i p f (l6_2 p f)) (l6_6ii_proved p f)

theorem l6_7_proved : L6_7 p f := l6_7 p f (l6_2 p f)

theorem l6_9_proved : L6_9 p f := l6_9 p f (l6_6_proved p f)

theorem l6_10_proved : L6_10 p f := l6_10 p f (l6_6_proved p f)

theorem l6_11_proved : L6_11 p f := l6_11 p f (l6_6_proved p f)

end CFSG.ClassicalInvolution.Asc77
