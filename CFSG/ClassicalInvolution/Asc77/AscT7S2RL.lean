module

public import CFSG.ClassicalInvolution.Asc77.AscT7RH
public import CFSG.ClassicalInvolution.Asc77.AscT7S2RE
public import CFSG.ClassicalInvolution.Asc77.AscT7S2RK

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime]

theorem c21_14_Y_disc_of_C3 (hC3 : C21_3 p f) : C21_14_Y_disc p f :=
  c21_14_Y_disc_of_S4 p f hC3 (T7S2R.ih8S4Star p f)

theorem c21_14_Y_disc_of_hyp51 (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f) :
    C21_14_Y_disc p f :=
  c21_14_Y_disc_of_C3 (c21_3_of_hyp51 hHt hHu)

variable (p f) in
theorem c21_2_final_S (hNT : G2D4Models.G2NonToralGenerate p) (hHt : TwinFrameHyp51t p f)
    (hHu : TwinFrameHyp51u p f) (hNC : C21_NormCent p f) : C21_2 p f :=
  c21_2_final_R p f hNT hHt hHu (c21_14_Y_disc_of_hyp51 hHt hHu) hNC

theorem thm7A_of_inputs₈
    (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f) (hNC : C21_NormCent p f)
    (hH22z : Hyp22Hyp51z p f) (hH22u : Hyp22Hyp51u p f) (h224σ : C22_4_sigma p f)
    (h224c : C22_4_cent p f) (h228 : C22_8 p f) (hchain22 : C22_chainSetting p f)
    (h234 : C23_4 p f) (h235 : C23_5 p f) (h237 : C23_7 p f) (hΓ : C23_Gamma p f)
    (hnoZ : C23_9_noZ p f) (hgen : C23_9_gen p f) (hchain23 : C23_chain p f)
    (h248 : C24_8 p f) (h249 : C24_9 p f) (hchain24 : C24_chain p f)
    (h2519 : C25_19_chain p f) (h2521 : C25_21_chain p f) : Thm7A p f :=
  thm7A_of_inputs₇ hHt hHu (c21_14_Y_disc_of_hyp51 hHt hHu) hNC hH22z hH22u h224σ h224c h228
    hchain22 h234 h235 h237 hΓ hnoZ hgen hchain23 h248 h249 hchain24 h2519 h2521

end CFSG.ClassicalInvolution.Asc77
