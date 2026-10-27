module

public import CFSG.ClassicalInvolution.Asc77.AscT7EExit24
public import CFSG.ClassicalInvolution.Asc77.AscIHSectH
public import CFSG.ClassicalInvolution.Asc77.AscT7ED2
public import CFSG.ClassicalInvolution.RouteD.G2D4G2NonToralFive
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDDischarge
public import CFSG.ClassicalInvolution.Asc77.AscT7BExit22S
public import CFSG.ClassicalInvolution.Asc77.AscT7BFinal23
public import CFSG.ClassicalInvolution.Asc77.AscT7CExit25

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime]

theorem thm7A_of_inputs₄
    (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f) (hD4 : Ih8D4Star p f)
    (h2113 : C21_13_N p f) (h2114 : C21_14_N p f) (h2114a : C21_14_alt p f) (h2115 : C21_15 p f)
    (hWyl : C21_WylTrans' p f)
    (hH22z : Hyp22Hyp51z p f) (hH22u : Hyp22Hyp51u p f) (h224σ : C22_4_sigma p f)
    (h224c : C22_4_cent p f) (h228 : C22_8 p f) (hchain22 : C22_chainSetting p f)
    (h234 : C23_4 p f) (h235 : C23_5 p f) (h237 : C23_7 p f) (hΓ : C23_Gamma p f)
    (hnoZ : C23_9_noZ p f) (hgen : C23_9_gen p f) (hchain23 : C23_chain p f)
    (h248 : C24_8 p f) (h249 : C24_9 p f) (hchain24 : C24_chain p f)
    (h2519 : C25_19_chain p f) (h2521 : C25_21_chain p f) : Thm7A p f := by
  intro G _ _ _ Ω K hst htw hdis
  have hNT := CFSG.ClassicalInvolution.G2D4Models.g2NonToralGenerate_all (p := p)
  exact (thm7A_of_steps (wz p f)
    (c21_2_final_H p f hNT hHt hHu hD4 h2113 h2114 h2114a h2115 hWyl)
    (c22_1_of_inputs' (thmEWithSylow_of_nonToral f hNT) hH22z hH22u h224σ h224c h228 hchain22)
    (c23_1_of thompsonCube thompsonStar c23_1_clique_proved)
    (c23_3_of_inputs' (thmEWithSylow_of_nonToral f hNT) (c23_2_trans_proved p f)
      (c23_setupSetting_proved p f) h234 h235 h237 hΓ hnoZ hgen hchain23
      (CFSG.ClassicalInvolution.RouteD.spinMinus6Generated_galois hst.odd))
    (c24_1_of_inputs'' h248 h249 hchain24)
    (c25_E4_of_inputs c25_RS_proved h2519 h2521)) G Ω K hst htw hdis

end CFSG.ClassicalInvolution.Asc77
