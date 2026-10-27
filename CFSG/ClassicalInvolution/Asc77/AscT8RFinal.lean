module

public import CFSG.ClassicalInvolution.Asc77.AscT8ROutF
public import CFSG.ClassicalInvolution.Asc77.AscT8S26VGlue
public import CFSG.ClassicalInvolution.Asc77.AscT8Y6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

variable (p f : ℕ) [Fact p.Prime]

theorem thm8A_of_five_residuals (hZ : S26XMuZ2 p f) (h13 : C26_13_sc p f) (hE : C27_8E4 p f)
    (hO : C27_Oab p f) (hY : C27_Ysmall p f) : Thm8A p f :=
  thm8A_of_core' (ih8D4Star (p := p) (f := f)) (c26_2_of_c26_1_muZ2 (T8R.c26_1 p f) hZ)
    (c26_13_of_sc h13) hE hO hY

end CFSG.ClassicalInvolution.Asc77
