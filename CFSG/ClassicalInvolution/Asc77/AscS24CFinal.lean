module

public import CFSG.ClassicalInvolution.Asc77.AscS24BFinal
public import CFSG.ClassicalInvolution.Asc77.AscS24CMain

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace S24

variable (p f : ℕ) [Fact p.Prime]


theorem c24_9_core_proved : C24_9_core p f :=
  S24B.c24_9_core_of_noGraph (noGraph_of p f S24B.h3_proved)

end S24

end CFSG.ClassicalInvolution.Asc77
