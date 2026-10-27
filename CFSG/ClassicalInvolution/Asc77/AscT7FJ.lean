module

public import CFSG.ClassicalInvolution.Asc77.AscT7FH
public import CFSG.ClassicalInvolution.Asc77.AscT7FI

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime]

variable (p f) in
theorem c21_2_final_J (hNT : G2D4Models.G2NonToralGenerate p) (hHt : TwinFrameHyp51t p f)
    (hHu : TwinFrameHyp51u p f) (h13 : C21_13_M_ne p f) (h14 : C21_14_N_disc p f)
    (h14a : C21_14_alt_rest p f) (h15 : C21_15 p f) : C21_2 p f :=
  c21_2_final_residual p f hNT hHt hHu h13 h14 h14a h15 (c21_starCent_proved p f)

variable (p f) in
theorem c21_2_final_J' (hNT : G2D4Models.G2NonToralGenerate p) (hHt : TwinFrameHyp51t p f)
    (hHu : TwinFrameHyp51u p f) (h13N : C21_13_N p f) (h14N : C21_14_N p f)
    (h14a : C21_14_alt p f) (h15 : C21_15 p f) : C21_2 p f :=
  c21_2_final_H' p f hNT hHt hHu h13N h14N h14a h15 (c21_starCent_proved p f)

theorem thm7A_of_inputs₆
    (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f)
    (h2113 : C21_13_M_ne p f) (h2114 : C21_14_N_disc p f) (h2114a : C21_14_alt_rest p f)
    (h2115 : C21_15 p f)
    (hH22z : Hyp22Hyp51z p f) (hH22u : Hyp22Hyp51u p f) (h224σ : C22_4_sigma p f)
    (h224c : C22_4_cent p f) (h228 : C22_8 p f) (hchain22 : C22_chainSetting p f)
    (h234 : C23_4 p f) (h235 : C23_5 p f) (h237 : C23_7 p f) (hΓ : C23_Gamma p f)
    (hnoZ : C23_9_noZ p f) (hgen : C23_9_gen p f) (hchain23 : C23_chain p f)
    (h248 : C24_8 p f) (h249 : C24_9 p f) (hchain24 : C24_chain p f)
    (h2519 : C25_19_chain p f) (h2521 : C25_21_chain p f) : Thm7A p f :=
  thm7A_of_inputs₅ hHt hHu h2113 h2114 h2114a h2115 (c21_starCent_proved p f) hH22z hH22u h224σ
    h224c h228 hchain22 h234 h235 h237 hΓ hnoZ hgen hchain23 h248 h249 hchain24 h2519 h2521

end CFSG.ClassicalInvolution.Asc77
