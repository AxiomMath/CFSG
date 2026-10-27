module

public import CFSG.ClassicalInvolution.Asc77.AscT7C2RFive
public import CFSG.ClassicalInvolution.Asc77.AscT7C2RChain
public import CFSG.ClassicalInvolution.Asc77.AscT7DRFive
public import CFSG.ClassicalInvolution.Asc77.AscT7DRLit
public import CFSG.ClassicalInvolution.Asc77.AscT7BExit22S
public import CFSG.ClassicalInvolution.Asc77.AscT7BFinal23
public import CFSG.ClassicalInvolution.Asc77.AscT7ED2
public import CFSG.ClassicalInvolution.Asc77.AscT7EExit24
public import CFSG.ClassicalInvolution.Asc77.AscT7FF
public import CFSG.ClassicalInvolution.Asc77.AscT7FI
public import CFSG.ClassicalInvolution.RouteD.G2D4G2NonToralFive
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDDischarge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime]

theorem c24_1_of_core (hcore : C24_9_core p f) (hbig : C24_8_big p f) (hpair : C24_pair p f) :
    C24_1 p f :=
  c24_1_of_inputs'' (T7C2.c24_8_of_big (T7C2.c24_9_of_core hcore) hbig)
    (T7C2.c24_9_of_core hcore) (c24_chain_of_pair hpair)

theorem c25_E4_of_exits (h19 : C25_19 p f) (h21 : C25_21 p f) : C25_E4 p f :=
  c25_E4_of_steps (c25_setup_of c25_RS_proved) h19 h21

theorem c25_E4_of_sylow (h2 : C25_2_t p f) (h17 : C25_17_idx p f) (h20 : C25_20 p f) :
    C25_E4 p f :=
  c25_E4_of_exits (c25_19_of_sylow p f h2 h17) (c25_21_of_sylow p f h20)

theorem thm7A_of_inputs₆Y
    (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f)
    (h2113 : C21_13_M_ne p f) (h2114 : C21_14_N_disc p f) (h2114a : C21_14_alt_rest p f)
    (h2115 : C21_15 p f)
    (hH22z : Hyp22Hyp51z p f) (hH22u : Hyp22Hyp51u p f) (h224σ : C22_4_sigma p f)
    (h224c : C22_4_cent p f) (h228 : C22_8 p f) (hchain22 : C22_chainSetting p f)
    (h234 : C23_4 p f) (h235 : C23_5 p f) (h237 : C23_7 p f) (hΓ : C23_Gamma p f)
    (hnoZ : C23_9_noZ p f) (hgen : C23_9_gen p f) (hchain23 : C23_chain p f)
    (hcore : C24_9_core p f) (hbig : C24_8_big p f) (hpair : C24_pair p f)
    (h2519 : C25_19 p f) (h2521 : C25_21 p f) : Thm7A p f := by
  intro G _ _ _ Ω K hst htw hdis
  have hNT := CFSG.ClassicalInvolution.G2D4Models.g2NonToralGenerate_all (p := p)
  exact (thm7A_of_steps (wz p f)
    (c21_2_final_residual p f hNT hHt hHu h2113 h2114 h2114a h2115 (c21_starCent_proved p f))
    (c22_1_of_inputs' (thmEWithSylow_of_nonToral f hNT) hH22z hH22u h224σ h224c h228 hchain22)
    (c23_1_of thompsonCube thompsonStar c23_1_clique_proved)
    (c23_3_of_inputs' (thmEWithSylow_of_nonToral f hNT) (c23_2_trans_proved p f)
      (c23_setupSetting_proved p f) h234 h235 h237 hΓ hnoZ hgen hchain23
      (CFSG.ClassicalInvolution.RouteD.spinMinus6Generated_galois hst.odd))
    (c24_1_of_core hcore hbig hpair)
    (c25_E4_of_steps (c25_setup_of c25_RS_proved) h2519 h2521)) G Ω K hst htw hdis

theorem thm7A_of_inputs₆Z
    (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f)
    (h2113 : C21_13_M_ne p f) (h2114 : C21_14_N_disc p f) (h2114a : C21_14_alt_rest p f)
    (h2115 : C21_15 p f)
    (hH22z : Hyp22Hyp51z p f) (hH22u : Hyp22Hyp51u p f) (h224σ : C22_4_sigma p f)
    (h224c : C22_4_cent p f) (h228 : C22_8 p f) (hchain22 : C22_chainSetting p f)
    (h234 : C23_4 p f) (h235 : C23_5 p f) (h237 : C23_7 p f) (hΓ : C23_Gamma p f)
    (hnoZ : C23_9_noZ p f) (hgen : C23_9_gen p f) (hchain23 : C23_chain p f)
    (hcore : C24_9_core p f) (hbig : C24_8_big p f) (hpair : C24_pair p f)
    (h252 : C25_2_t p f) (h2517 : C25_17_idx p f) (h2520 : C25_20 p f) : Thm7A p f :=
  thm7A_of_inputs₆Y hHt hHu h2113 h2114 h2114a h2115 hH22z hH22u h224σ h224c h228 hchain22 h234
    h235 h237 hΓ hnoZ hgen hchain23 hcore hbig hpair (c25_19_of_sylow p f h252 h2517)
    (c25_21_of_sylow p f h2520)

end CFSG.ClassicalInvolution.Asc77
