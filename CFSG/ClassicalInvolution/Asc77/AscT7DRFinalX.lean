module

public import CFSG.ClassicalInvolution.Asc77.AscT7DRFinal
public import CFSG.ClassicalInvolution.Asc77.AscT7HSeven
public import CFSG.ClassicalInvolution.Asc77.AscT7HX22
public import CFSG.ClassicalInvolution.Asc77.AscT7HX23
public import CFSG.ClassicalInvolution.Asc77.AscT7S22Sigma
public import CFSG.ClassicalInvolution.Asc77.AscT7S22Z

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime]

theorem thm7A_of_inputs₆XY
    (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f)
    (h2113 : C21_13_M_ne p f) (h2114 : C21_14_N_disc p f) (h2114a : C21_14_alt_rest p f)
    (h2115 : C21_15 p f)
    (hH22u : Hyp22Hyp51u p f) (h224c : C22_4_cent p f) (h228 : C22_8X p f)
    (hchain22 : C22_chainSettingX p f)
    (h234 : C23_4X p f) (h235 : C23_5X p f) (hΓ : C23_Gamma p f)
    (hnoZ : C23_9_noZX p f) (hgen : C23_9_genX p f) (hchain23 : C23_chainX p f)
    (hcore : C24_9_core p f) (hbig : C24_8_big p f) (hpair : C24_pair p f)
    (h2519 : C25_19 p f) (h2521 : C25_21 p f) : Thm7A p f := by
  intro G _ _ _ Ω K hst htw hdis
  have hNT := CFSG.ClassicalInvolution.G2D4Models.g2NonToralGenerate_all (p := p)
  exact (thm7A_of_steps (wz p f)
    (c21_2_final_residual p f hNT hHt hHu h2113 h2114 h2114a h2115 (c21_starCent_proved p f))
    (c22_1_of_inputsX (thmEWithSylow_of_nonToral f hNT) (hyp22Hyp51z p f) hH22u
      (c22_4_sigma_proved p f) h224c h228 hchain22)
    (c23_1_of thompsonCube thompsonStar c23_1_clique_proved)
    (c23_3_of_inputsX (thmEWithSylow_of_nonToral f hNT) (c23_2_trans_proved p f)
      (c23_setupSetting_proved p f) h234 h235 c23_7_proved hΓ hnoZ hgen hchain23
      (CFSG.ClassicalInvolution.RouteD.spinMinus6Generated_galois hst.odd))
    (c24_1_of_core hcore hbig hpair)
    (c25_E4_of_steps (c25_setup_of c25_RS_proved) h2519 h2521)) G Ω K hst htw hdis

theorem thm7A_of_inputs₆XZ
    (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f)
    (h2113 : C21_13_M_ne p f) (h2114 : C21_14_N_disc p f) (h2114a : C21_14_alt_rest p f)
    (h2115 : C21_15 p f)
    (hH22u : Hyp22Hyp51u p f) (h224c : C22_4_cent p f) (h228 : C22_8X p f)
    (hchain22 : C22_chainSettingX p f)
    (h234 : C23_4X p f) (h235 : C23_5X p f) (hΓ : C23_Gamma p f)
    (hnoZ : C23_9_noZX p f) (hgen : C23_9_genX p f) (hchain23 : C23_chainX p f)
    (hcore : C24_9_core p f) (hbig : C24_8_big p f) (hpair : C24_pair p f)
    (h252 : C25_2_t p f) (h2517 : C25_17_idx p f) (h2520 : C25_20 p f) : Thm7A p f :=
  thm7A_of_inputs₆XY hHt hHu h2113 h2114 h2114a h2115 hH22u h224c h228 hchain22 h234 h235 hΓ
    hnoZ hgen hchain23 hcore hbig hpair (c25_19_of_sylow p f h252 h2517)
    (c25_21_of_sylow p f h2520)

end CFSG.ClassicalInvolution.Asc77
