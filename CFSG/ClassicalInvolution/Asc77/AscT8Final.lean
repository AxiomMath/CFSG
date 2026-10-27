module

public import CFSG.ClassicalInvolution.Asc77.AscT8Route
public import CFSG.ClassicalInvolution.Asc77.AscT8Lie

public section

namespace CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime]

theorem cf26_of_c26_7 (h7 : C26_7 p f) : CF26 p f :=
  cf26_of_steps h7 c26_L5_proved

theorem thm8A_of_residuals (h26_2 : C26_2 p f) (h26_13 : C26_13 p f) (h26_7 : C26_7 p f)
    (h274a : C27_4a p f) (h278 : C27_8 p f) : Thm8A p f :=
  thm8A_of_inputs h26_2 h26_13 h26_7 c26_L5_proved h274a h278

end CFSG.ClassicalInvolution.Asc77
