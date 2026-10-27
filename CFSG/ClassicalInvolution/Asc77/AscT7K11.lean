module

public import CFSG.ClassicalInvolution.Asc77.AscT7K10

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.LieType.Universal

variable {p f : ℕ} [Fact p.Prime]

theorem c23_9_ofK (h2 : C23_2 p f) (h4 : C23_4X p f) (h5 : C23_5X_type p f) (h7 : C23_7 p f)
    (hΓu : C23_GammaU p f) (hnoZ : C23_9_noZX p f) (hgen : C23_9_genX p f) : C23_9X p f := by
  intro G _ _ _ Ω K K' W z u e g h
  have hE : LayerOrthType p f Ω e 6 (piSign p f) :=
    (h4 G Ω K K' W z u e g h).resolve_left (h7 G Ω K K' W z u e g h)
  have hset : Hyp23Setting p f Ω K K' z := h.std.setting
  obtain ⟨hodd, halpha⟩ := T7K.c23_5X_one_proved hset h.data
  have hY : u * e ∈ zStarOf (rLayer Ω u) ∨ LayerOrthType p f Ω u 5 true ∨
      LayerOrthType p f Ω u 6 (!piSign p f) := h5 G Ω K K' W z u e g h
  have hY' : LayerOrthType p f Ω u 5 true ∨ LayerOrthType p f Ω u 6 (!piSign p f) :=
    hY.resolve_left (hnoZ G Ω K K' W z u e g hset h.data hE)
  have hΓz := T7K.centralizer_z_le_gamma2 hset h.data
  have hΓu' := hΓu G Ω K K' W z u e g hset h.data
  have hG := h2 G Ω K K' z h.std W h.hW h.hzW u h.hu h.huW h.hu1 h.huz h.hu2
  have hN : Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hG]
    exact sup_le (hΓu'.trans (gamma2_le_normalizer_alphaOf halpha _))
      (hΓz.trans (gamma2_le_normalizer_alphaOf halpha _))
  have hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥ :=
    T7B.eq_bot_of_normalizer_eq_top hodd hN (T7B.two_dvd_natCard h.std.1.hz)
  exact ⟨⟨hα, hgen G Ω K K' W z u e g hset h.data hE hY'⟩, hE, hY'⟩

theorem c23_3_of_inputsK (hE : ThmEWithSylow p f) (htr : C23_2_trans p f)
    (hsetup : C23_setupSetting p f) (h4 : C23_4X p f) (h5 : C23_5X_type p f) (h7 : C23_7 p f)
    (hΓu : C23_GammaU p f) (hnoZ : C23_9_noZX p f) (hgen : C23_9_genX p f)
    (hchain : C23_chainX p f) (hg6 : SpinMinus6Generated (minusCoeffs_irr p f)) : C23_3 p f :=
  c23_3_of_steps (c23_setup_of hsetup)
    (c23_10_ofX (c23_9_ofK (c23_2_of_trans hE htr) h4 h5 h7 hΓu hnoZ hgen) hchain hg6)

end CFSG.ClassicalInvolution.Asc77
