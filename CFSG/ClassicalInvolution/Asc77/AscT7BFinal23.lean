module

public import CFSG.ClassicalInvolution.Asc77.AscT7BFuse23
public import CFSG.ClassicalInvolution.Asc77.AscT7BExit23

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.LieType.Universal CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime]

theorem c23_2_of_trans (hE : ThmEWithSylow p f) (htr : C23_2_trans p f) : C23_2 p f :=
  c23_2_of hE htr c23_2_fuse

theorem c23_3_of_inputs' (hE : ThmEWithSylow p f) (htr : C23_2_trans p f)
    (hsetup : C23_setupSetting p f) (h4 : C23_4 p f) (h5 : C23_5 p f) (h7 : C23_7 p f)
    (hΓ : C23_Gamma p f) (hnoZ : C23_9_noZ p f) (hgen : C23_9_gen p f) (hchain : C23_chain p f)
    (hg6 : SpinMinus6Generated (minusCoeffs_irr p f)) : C23_3 p f :=
  c23_3_of_inputs hE htr c23_2_fuse hsetup h4 h5 h7 hΓ hnoZ hgen hchain hg6

end CFSG.ClassicalInvolution.Asc77
