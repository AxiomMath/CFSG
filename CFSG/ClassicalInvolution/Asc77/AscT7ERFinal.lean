module

public import CFSG.ClassicalInvolution.Asc77.AscT7ERIdx
public import CFSG.ClassicalInvolution.Asc77.AscT7DRFinalX

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime]

theorem c25_19_of_idx (h17 : C25_17_idx p f) : C25_19 p f :=
  c25_19_of_sylow p f (c25_2_t_proved p f) h17

theorem c25_E4_of_idx (h17 : C25_17_idx p f) (h20 : C25_20 p f) : C25_E4 p f :=
  c25_E4_of_sylow (c25_2_t_proved p f) h17 h20

theorem thm7A_of_inputs₆XZ'
    (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f)
    (h2113 : C21_13_M_ne p f) (h2114 : C21_14_N_disc p f) (h2114a : C21_14_alt_rest p f)
    (h2115 : C21_15 p f)
    (hH22u : Hyp22Hyp51u p f) (h224c : C22_4_cent p f) (h228 : C22_8X p f)
    (hchain22 : C22_chainSettingX p f)
    (h234 : C23_4X p f) (h235 : C23_5X p f) (hΓ : C23_Gamma p f)
    (hnoZ : C23_9_noZX p f) (hgen : C23_9_genX p f) (hchain23 : C23_chainX p f)
    (hcore : C24_9_core p f) (hbig : C24_8_big p f) (hpair : C24_pair p f)
    (h2517 : C25_17_idx p f) (h2520 : C25_20 p f) : Thm7A p f :=
  thm7A_of_inputs₆XZ hHt hHu h2113 h2114 h2114a h2115 hH22u h224c h228 hchain22 h234 h235 hΓ
    hnoZ hgen hchain23 hcore hbig hpair (c25_2_t_proved p f) h2517 h2520

theorem thm7A_of_inputs₆XN
    (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f)
    (h2113 : C21_13_M_ne p f) (h2114 : C21_14_N_disc p f) (h2114a : C21_14_alt_rest p f)
    (h2115 : C21_15 p f)
    (hH22u : Hyp22Hyp51u p f) (h224c : C22_4_cent p f) (h228 : C22_8X p f)
    (hchain22 : C22_chainSettingX p f)
    (h234 : C23_4X p f) (h235 : C23_5X p f) (hΓ : C23_Gamma p f)
    (hnoZ : C23_9_noZX p f) (hgen : C23_9_genX p f) (hchain23 : C23_chainX p f)
    (hcore : C24_9_core p f) (hbig : C24_8_big p f) (hpair : C24_pair p f)
    (h2517 : C25_17_norm p f) (h2520 : C25_20 p f) : Thm7A p f :=
  thm7A_of_inputs₆XZ' hHt hHu h2113 h2114 h2114a h2115 hH22u h224c h228 hchain22 h234 h235 hΓ
    hnoZ hgen hchain23 hcore hbig hpair (c25_17_idx_of_norm p f h2517) h2520

end CFSG.ClassicalInvolution.Asc77
