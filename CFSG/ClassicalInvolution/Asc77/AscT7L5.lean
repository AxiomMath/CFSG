module

public import CFSG.ClassicalInvolution.Asc77.AscT7L4
public import CFSG.ClassicalInvolution.Asc77.AscT7K11

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.LieType.Universal

variable {p f : ℕ} [Fact p.Prime]

theorem c23_5X_type_of_tcf (htcf : TwinCentralFact p) : C23_5X_type p f := by
  intro G _ _ _ Ω K K' W z u e g h
  have hs : Hyp23Setting p f Ω K K' z := h.std.setting
  have hd : Hyp23bData Ω K K' W z u e g := h.data
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hrl : rLayer Ω u = exactLayer Ω u :=
    rLayer_eq_exactLayer hs.stand.odd hs.stand.five hΩ hd.hu2
  rw [hrl]
  exact T7L.layer_u_tag htcf hs hd

theorem c23_9_ofL (htcf : TwinCentralFact p) (h2 : C23_2 p f) (h4 : C23_4X p f)
    (h7 : C23_7 p f) (hΓu : C23_GammaU p f) (hnoZ : C23_9_noZX p f) (hgen : C23_9_genX p f) :
    C23_9X p f :=
  c23_9_ofK h2 h4 (c23_5X_type_of_tcf htcf) h7 hΓu hnoZ hgen

theorem c23_3_of_inputsL (htcf : TwinCentralFact p) (hE : ThmEWithSylow p f)
    (htr : C23_2_trans p f) (hsetup : C23_setupSetting p f) (h4 : C23_4X p f)
    (h7 : C23_7 p f) (hΓu : C23_GammaU p f) (hnoZ : C23_9_noZX p f) (hgen : C23_9_genX p f)
    (hchain : C23_chainX p f) (hg6 : SpinMinus6Generated (minusCoeffs_irr p f)) :
    C23_3 p f :=
  c23_3_of_inputsK hE htr hsetup h4 (c23_5X_type_of_tcf htcf) h7 hΓu hnoZ hgen hchain hg6

end CFSG.ClassicalInvolution.Asc77
