module

public import CFSG.ClassicalInvolution.Asc77.AscT8S26NoF
public import CFSG.ClassicalInvolution.Asc77.AscT8MinProof
public import CFSG.ClassicalInvolution.Asc77.AscT8Y

public section

namespace CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime]

theorem thm8A_of_c27_Y (h2 : C26_2 p f) (h13 : C26_13 p f) (hY : C27_Y p f) : Thm8A p f :=
  thm8A_of_c26_2_c26_13 h2 h13 (c27_4a_of_min (c27_2_of_c26_2_c26_13 h2 h13) c27_4M_proved)
    (c27_8_of_c27_Y hY)

theorem thm8A_of_c27_6_c27_7 (h2 : C26_2 p f) (h13 : C26_13 p f) (h6 : C27_6 p f)
    (h7 : C27_7 p f) : Thm8A p f :=
  thm8A_of_c27_Y h2 h13 (c27_Y_of_c27_6_c27_7 h6 h7)

end CFSG.ClassicalInvolution.Asc77
