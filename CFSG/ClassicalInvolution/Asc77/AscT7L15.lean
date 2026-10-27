module

public import CFSG.ClassicalInvolution.Asc77.AscT7L5
public import CFSG.ClassicalInvolution.Asc77.AscT7L9
public import CFSG.ClassicalInvolution.Asc77.AscT7L11
public import CFSG.ClassicalInvolution.Asc77.AscT7L12
public import CFSG.ClassicalInvolution.Asc77.AscT7L14

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.LieType.Universal

variable {p f : ℕ} [Fact p.Prime]

theorem twinCentralFact_proved : TwinCentralFact p :=
  twinCentralFact_of_rows (T7L.twinCentralSL p) (T7L.twinCentralSU p) (T7L.twinCentralSpin7 p)
    (T7L.twinCentralD4P p) (T7L.twinCentralD4M p)

theorem c23_5X_type_proved : C23_5X_type p f :=
  c23_5X_type_of_tcf twinCentralFact_proved

theorem c23_GammaU_of_e4 (hgen : E4TwinGen p) : C23_GammaU p f :=
  c23_GammaU_of_facts twinCentralFact_proved hgen

theorem c23_9_ofL' (hgen : E4TwinGen p) (h2 : C23_2 p f) (h4 : C23_4X p f) (h7 : C23_7 p f)
    (hnoZ : C23_9_noZX p f) (hgenX : C23_9_genX p f) : C23_9X p f :=
  c23_9_ofL twinCentralFact_proved h2 h4 h7 (c23_GammaU_of_e4 hgen) hnoZ hgenX

theorem c23_3_of_inputsL' (hgen : E4TwinGen p) (hE : ThmEWithSylow p f) (htr : C23_2_trans p f)
    (hsetup : C23_setupSetting p f) (h4 : C23_4X p f) (h7 : C23_7 p f)
    (hnoZ : C23_9_noZX p f) (hgenX : C23_9_genX p f) (hchain : C23_chainX p f)
    (hg6 : SpinMinus6Generated (minusCoeffs_irr p f)) : C23_3 p f :=
  c23_3_of_inputsL twinCentralFact_proved hE htr hsetup h4 h7 (c23_GammaU_of_e4 hgen) hnoZ hgenX
    hchain hg6

end CFSG.ClassicalInvolution.Asc77
