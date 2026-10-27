module

public import CFSG.ClassicalInvolution.Asc77.AscT7FF
public import CFSG.ClassicalInvolution.Asc77.AscT7BExit22S
public import CFSG.ClassicalInvolution.Asc77.AscT7BFinal23
public import CFSG.ClassicalInvolution.Asc77.AscT7CExit25
public import CFSG.ClassicalInvolution.Asc77.AscT7ED2
public import CFSG.ClassicalInvolution.Asc77.AscT7EExit24
public import CFSG.ClassicalInvolution.RouteD.G2D4G2NonToralFive
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDDischarge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime]

theorem thm7A_of_inputs₅
    (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f)
    (h2113 : C21_13_M_ne p f) (h2114 : C21_14_N_disc p f) (h2114a : C21_14_alt_rest p f)
    (h2115 : C21_15 p f) (hStar : C21_StarCent p f)
    (hH22z : Hyp22Hyp51z p f) (hH22u : Hyp22Hyp51u p f) (h224σ : C22_4_sigma p f)
    (h224c : C22_4_cent p f) (h228 : C22_8 p f) (hchain22 : C22_chainSetting p f)
    (h234 : C23_4 p f) (h235 : C23_5 p f) (h237 : C23_7 p f) (hΓ : C23_Gamma p f)
    (hnoZ : C23_9_noZ p f) (hgen : C23_9_gen p f) (hchain23 : C23_chain p f)
    (h248 : C24_8 p f) (h249 : C24_9 p f) (hchain24 : C24_chain p f)
    (h2519 : C25_19_chain p f) (h2521 : C25_21_chain p f) : Thm7A p f := by
  intro G _ _ _ Ω K hst htw hdis
  have hNT := CFSG.ClassicalInvolution.G2D4Models.g2NonToralGenerate_all (p := p)
  exact (thm7A_of_steps (wz p f)
    (c21_2_final_residual p f hNT hHt hHu h2113 h2114 h2114a h2115 hStar)
    (c22_1_of_inputs' (thmEWithSylow_of_nonToral f hNT) hH22z hH22u h224σ h224c h228 hchain22)
    (c23_1_of thompsonCube thompsonStar c23_1_clique_proved)
    (c23_3_of_inputs' (thmEWithSylow_of_nonToral f hNT) (c23_2_trans_proved p f)
      (c23_setupSetting_proved p f) h234 h235 h237 hΓ hnoZ hgen hchain23
      (CFSG.ClassicalInvolution.RouteD.spinMinus6Generated_galois hst.odd))
    (c24_1_of_inputs'' h248 h249 hchain24)
    (c25_E4_of_inputs c25_RS_proved h2519 h2521)) G Ω K hst htw hdis

variable (p f) in
theorem c21_2_final_H' (hNT : G2D4Models.G2NonToralGenerate p) (hHt : TwinFrameHyp51t p f)
    (hHu : TwinFrameHyp51u p f) (h13N : C21_13_N p f) (h14N : C21_14_N p f)
    (h14a : C21_14_alt p f) (h15 : C21_15 p f) (hStar : C21_StarCent p f) : C21_2 p f := by
  by_cases hpq : p ≠ 2 ∧ 5 ≤ p ^ f
  · have hMF : DStarConnectedTwinGen p f :=
      dstarConnectedTwinGen_of smallNoThree G2D4Models.ih8G2D4_unconditional ih8D4Star hpq.1 hpq.2
    have h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n :=
      G2D4Models.h3s_of_nonToral_free hNT
    exact c21_2_final_sect'' p f (thmEWithSylow_of_nonToral f hNT) (twinFrameHyp51z p f) hHt hHu
      (c21_12_proved p f) hMF h3s h13N h14N h14a h15 hStar (c21_YSigma_of_sections p f h3s)
  · intro G _ _ _ Ω K K' z hs
    exact absurd ⟨hs.stand.odd, hs.stand.five⟩ hpq

end CFSG.ClassicalInvolution.Asc77
