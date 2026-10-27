module

public import CFSG.ClassicalInvolution.Q3.TL4VtxMainC
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Model

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.ClassicalInvolution

theorem e4AutOddFreeR_proved : E4AutOddFreeR :=
  fun _ _ _ hM => Vtx.autOddFree_of_exLie hM

section Final

variable {n : ℕ}

theorem tightHyp51TriR_three_of_components (h4 : Thm4RBelow 3 n) (h5 : Thm5RBelowF 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetBelow n) : TightHyp51TriR 3 n :=
  tightHyp51TriR_three_of_thm5 h4 h5 htw e4AutOddFreeR_proved

end Final

end CFSG.ClassicalInvolution.Q3.TL4
