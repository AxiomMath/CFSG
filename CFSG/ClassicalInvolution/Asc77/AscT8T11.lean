module

public import CFSG.ClassicalInvolution.Asc77.AscT8T10
public import CFSG.ClassicalInvolution.Asc77.AscT8S2Final

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

variable (p f : ℕ) [Fact p.Prime]


theorem thm8A_of_residuals_alphaNorm (h13 : C26_13_sc p f) (hE : C27_8E4 p f)
    (hY : C27_Ysmall p f) (hN : T8T.C27_AlphaNorm p f) : Thm8A p f := by
  have h26_2 : C26_2 p f := c26_2_of_c26_1_muZ2 (T8R.c26_1 p f) s26XMuZ2_proved
  have h26_13 : C26_13 p f := c26_13_of_sc h13
  have h2 : C27_2 p f := c27_2_of_c26_2_c26_13 h26_2 h26_13
  have h4a : C27_4a p f := c27_4a_of_min h2 c27_4M_proved
  exact thm8A_of_four_residuals p f h13 hE (c27_Oab_of_alphaNorm p f h2 h4a hN) hY

theorem thm8A_of_residuals_alphaConst (h13 : C26_13_sc p f) (hE : C27_8E4 p f)
    (hY : C27_Ysmall p f) (hA : T8T.C27_AlphaConst p f) : Thm8A p f := by
  have h26_2 : C26_2 p f := c26_2_of_c26_1_muZ2 (T8R.c26_1 p f) s26XMuZ2_proved
  have h26_13 : C26_13 p f := c26_13_of_sc h13
  have h2 : C27_2 p f := c27_2_of_c26_2_c26_13 h26_2 h26_13
  exact thm8A_of_residuals_alphaNorm p f h13 hE hY
    (c27_alphaNorm_of_alphaConst p f (ih8D4Star (p := p) (f := f)) h2 hA)

end CFSG.ClassicalInvolution.Asc77
