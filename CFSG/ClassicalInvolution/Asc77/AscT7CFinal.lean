module

public import CFSG.ClassicalInvolution.Asc77.AscT7CExit24
public import CFSG.ClassicalInvolution.Asc77.AscT7CExit25
public import CFSG.ClassicalInvolution.Asc77.AscT7AU
public import CFSG.ClassicalInvolution.Asc77.AscT7BExit22S
public import CFSG.ClassicalInvolution.Asc77.AscT7BMu23
public import CFSG.ClassicalInvolution.Asc77.AscT7BFinal23

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime]

theorem thm7A_of_h (h21 : C21_2 p f) (h22 : C22_1 p f) (h231 : C23_1 p f) (h233 : C23_3 p f)
    (h242 : C24_2 p f) (h244 : C24_4 p f) (h247 : C24_7 p f) (h248 : C24_8 p f)
    (h249 : C24_9 p f) (hchain24 : C24_chain p f) (hRS : C25_RS p f)
    (h2519 : C25_19_chain p f) (h2521 : C25_21_chain p f) : Thm7A p f :=
  thm7A_of_steps (wz p f) h21 h22 h231 h233
    (c24_1_of_inputs h242 h244 h247 h248 h249 hchain24)
    (c25_E4_of_inputs hRS h2519 h2521)

theorem thm7A_of_inputs (hE : ThmEWithSylow p f)
    (hHz : TwinFrameHyp51z p f) (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f)
    (hMF : DStarConnectedTwin p f)
    (h3s : ∀ n : ℕ, CITBelowU p f n → T3.Thm3SectBelow p f n)
    (h2113 : C21_13_N p f) (h2114 : C21_14_N p f) (h2114a : C21_14_alt p f) (h2115 : C21_15 p f)
    (hWyl : C21_WylTrans' p f)
    (hH22z : Hyp22Hyp51z p f) (hH22u : Hyp22Hyp51u p f) (h224σ : C22_4_sigma p f)
    (h224c : C22_4_cent p f) (h228 : C22_8 p f) (hchain22 : C22_chainSetting p f)
    (hCube : ThompsonCube p f) (hStar : ThompsonStar p f) (hclique : C23_1_clique p f)
    (htr : C23_2_trans p f) (hsetup23 : C23_setupSetting p f) (h234 : C23_4 p f)
    (h235 : C23_5 p f) (h237 : C23_7 p f) (hΓ : C23_Gamma p f) (hnoZ : C23_9_noZ p f)
    (hgen : C23_9_gen p f) (hchain23 : C23_chain p f)
    (hg6 : CFSG.ClassicalInvolution.RouteD.SpinMinus6Generated
      (CFSG.LieType.Universal.minusCoeffs_irr p f))
    (h242 : C24_2 p f) (h244 : C24_4 p f) (h247 : C24_7 p f) (h248 : C24_8 p f)
    (h249 : C24_9 p f) (hchain24 : C24_chain p f)
    (hRS : C25_RS p f) (h2519 : C25_19_chain p f) (h2521 : C25_21_chain p f) : Thm7A p f :=
  thm7A_of_h
    (c21_2_final_sections p f hE hHz hHt hHu hMF h3s h2113 h2114 h2114a h2115 hWyl)
    (c22_1_of_inputs' hE hH22z hH22u h224σ h224c h228 hchain22)
    (c23_1_of hCube hStar hclique)
    (c23_3_of_inputs' hE htr hsetup23 h234 h235 h237 hΓ hnoZ hgen hchain23 hg6)
    h242 h244 h247 h248 h249 hchain24 hRS h2519 h2521

end CFSG.ClassicalInvolution.Asc77
