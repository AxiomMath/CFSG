module

public import CFSG.ClassicalInvolution.Asc77.AscT7F2Fus
public import CFSG.ClassicalInvolution.Asc77.AscT7ERFinal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]


theorem c25_17_norm_of_11_16 (h11 : C25_11 p f) (h16 : C25_16 p f) : C25_17_norm p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
  obtain ⟨t', ht'S, ⟨g, hg⟩, hconj⟩ := c25_2_t_proved p f G Ω K K' W S R R' z t u₁ u₂ hyp
  have hzz : z * z = 1 := hyp.std.setting.hz.sq
  have ht'2 : t' * t' = 1 := by
    rw [← hg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  have h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t' := ⟨hyp, ht'S, ht'2, hconj⟩
  by_contra hlt
  push Not at hlt
  exact h.false_of_d8 h11 h16 hlt

theorem c25_17_idx_of_11_16 (h11 : C25_11 p f) (h16 : C25_16 p f) : C25_17_idx p f :=
  c25_17_idx_of_norm p f (c25_17_norm_of_11_16 p f h11 h16)

variable {p f}

theorem thm7A_of_inputs₆X1116
    (hHt : TwinFrameHyp51t p f) (hHu : TwinFrameHyp51u p f)
    (h2113 : C21_13_M_ne p f) (h2114 : C21_14_N_disc p f) (h2114a : C21_14_alt_rest p f)
    (h2115 : C21_15 p f)
    (hH22u : Hyp22Hyp51u p f) (h224c : C22_4_cent p f) (h228 : C22_8X p f)
    (hchain22 : C22_chainSettingX p f)
    (h234 : C23_4X p f) (h235 : C23_5X p f) (hΓ : C23_Gamma p f)
    (hnoZ : C23_9_noZX p f) (hgen : C23_9_genX p f) (hchain23 : C23_chainX p f)
    (hcore : C24_9_core p f) (hbig : C24_8_big p f) (hpair : C24_pair p f)
    (h2511 : C25_11 p f) (h2516 : C25_16 p f) (h2520 : C25_20 p f) : Thm7A p f :=
  thm7A_of_inputs₆XN hHt hHu h2113 h2114 h2114a h2115 hH22u h224c h228 hchain22 h234 h235 hΓ
    hnoZ hgen hchain23 hcore hbig hpair (c25_17_norm_of_11_16 p f h2511 h2516) h2520

end CFSG.ClassicalInvolution.Asc77
