module

public import CFSG.ClassicalInvolution.Asc77.AscT7Y2
public import CFSG.ClassicalInvolution.Asc77.AscE18FromNT
public import CFSG.ClassicalInvolution.RouteD.G2D4G2NonToralFive
public import CFSG.ClassicalInvolution.Asc77.AscT7ED2
public import CFSG.ClassicalInvolution.Asc77.AscT7L25

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution

variable {p f : ℕ} [Fact p.Prime]

theorem c23_9_noZX_of (hE : ThmEWithSylow p f) : C23_9_noZX p f := by
  intro G _ _ _ Ω K K' W z u e g hs hd _
  exact T7Y.not_mem_zStar twinCentralFact_proved e4TwinGen_proved
    (T7Y.sup_centralizer_eq_top hE (c23_2_trans_proved p f) hs hd)
    (c23_GammaU_proved G Ω K K' W z u e g hs hd) hs hd

theorem c23_9_genX_of (hE : ThmEWithSylow p f) : C23_9_genX p f := by
  intro G _ _ _ Ω K K' W z u e g hs hd _ _
  exact T7Y.sup_layers_eq_top twinCentralFact_proved e4TwinGen_proved
    (T7Y.sup_centralizer_eq_top hE (c23_2_trans_proved p f) hs hd)
    (c23_GammaU_proved G Ω K K' W z u e g hs hd) hs hd

theorem c23_9_noZX_proved : C23_9_noZX p f :=
  c23_9_noZX_of (thmEWithSylow_of_nonToral f G2D4Models.g2NonToralGenerate_all)

theorem c23_9_genX_proved : C23_9_genX p f :=
  c23_9_genX_of (thmEWithSylow_of_nonToral f G2D4Models.g2NonToralGenerate_all)

end CFSG.ClassicalInvolution.Asc77
