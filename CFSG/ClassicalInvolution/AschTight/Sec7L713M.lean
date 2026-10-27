module

public import CFSG.ClassicalInvolution.AschTight.Sec7L713L
public import CFSG.ClassicalInvolution.AschTight.Sec71Main

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

variable (p f : ℕ) [Fact p.Prime]

theorem l7_13_mod : L7_13ModTmp p f := l7_13ModTmp_of p f (Sec71.l7_1_proved p f)

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
