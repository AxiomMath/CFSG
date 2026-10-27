module

public import CFSG.ClassicalInvolution.Asc77.AscT7HS6
public import CFSG.ClassicalInvolution.Asc77.AscT7JFrame
public import CFSG.ClassicalInvolution.Asc77.AscT7JCent

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime]

theorem thm7A_of_inputs₆XJ
    (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f)
    (h2113 : C21_13_M_ne p f) (h2114 : C21_14_N_disc p f) (h2114a : C21_14_alt_rest p f)
    (h2115 : C21_15 p f)
    (hres : TwinSqAlphaRows p) (h4 : Hyp22FourTwins p f) (hF : Hyp22Fuse p f)
    (hgen22 : C22_8Gen p f) (hZ : Hyp22ZStarCu p f) (hchain22 : C22_chainSettingX p f)
    (h235 : C23_5X p f) (hΓ : C23_Gamma p f)
    (hnoZ : C23_9_noZX p f) (hgen : C23_9_genX p f) (hchain23 : C23_chainX p f)
    (h248 : C24_8 p f) (h249 : C24_9 p f) (hchain24 : C24_chain p f)
    (h2519 : C25_19_chain p f) (h2521 : C25_21_chain p f) : Thm7A p f :=
  thm7A_of_inputs₆XP hHt hHu h2113 h2114 h2114a h2115
    (hyp22Hyp51u_of_fourthTwin hres (hyp22FourthTwin_of_fourTwins h4)) (c22_4_cent_of_zstar hZ)
    (c22_8X_of_inputs h4 hF hgen22) hchain22 h235 hΓ hnoZ hgen hchain23 h248 h249 hchain24
    h2519 h2521

end CFSG.ClassicalInvolution.Asc77
