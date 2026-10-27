module

public import CFSG.ClassicalInvolution.Asc77.AscT7L15
public import CFSG.ClassicalInvolution.Asc77.AscT7L18
public import CFSG.ClassicalInvolution.Asc77.AscT7L21
public import CFSG.ClassicalInvolution.Asc77.AscT7L24

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.LieType.Universal

variable {p f : ℕ} [Fact p.Prime]

theorem e4TwinGen_proved : E4TwinGen p :=
  e4TwinGen_of_rows (T7L.e4GenSp p) (T7L.e4GenSL p) (T7L.e4GenSU p)

theorem c23_GammaU_proved : C23_GammaU p f :=
  c23_GammaU_of_e4 e4TwinGen_proved

theorem c23_9_ofL'' (h2 : C23_2 p f) (h4 : C23_4X p f) (h7 : C23_7 p f)
    (hnoZ : C23_9_noZX p f) (hgenX : C23_9_genX p f) : C23_9X p f :=
  c23_9_ofL' e4TwinGen_proved h2 h4 h7 hnoZ hgenX

theorem c23_3_of_inputsL'' (hE : ThmEWithSylow p f) (htr : C23_2_trans p f)
    (hsetup : C23_setupSetting p f) (h4 : C23_4X p f) (h7 : C23_7 p f)
    (hnoZ : C23_9_noZX p f) (hgenX : C23_9_genX p f) (hchain : C23_chainX p f)
    (hg6 : SpinMinus6Generated (minusCoeffs_irr p f)) : C23_3 p f :=
  c23_3_of_inputsL' e4TwinGen_proved hE htr hsetup h4 h7 hnoZ hgenX hchain hg6

end CFSG.ClassicalInvolution.Asc77
