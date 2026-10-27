module

public import CFSG.ClassicalInvolution.Asc77.AscS24BEnd
public import CFSG.ClassicalInvolution.Asc77.AscS24BHEnd

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace S24B

variable {p f : ℕ} [Fact p.Prime]


theorem c24_9_core_of_noGraph (hng : NoGraph p f) : C24_9_core p f :=
  c24_9_core_of h3_proved hng

end S24B

end CFSG.ClassicalInvolution.Asc77
