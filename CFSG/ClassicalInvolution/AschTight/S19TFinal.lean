module

public import CFSG.ClassicalInvolution.AschTight.S19TMain
public import CFSG.ClassicalInvolution.AschTight.S19KFL

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]

theorem c19_11b_proved : C19_11bTmp p f :=
  c19_11b_of' p f S19K.factFL

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19T
