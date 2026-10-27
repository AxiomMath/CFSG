module

public import CFSG.ClassicalInvolution.Phan.PhanS16Final
public import CFSG.ClassicalInvolution.Phan.PhanS27Final

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.ClassicalInvolution.PhanB3.H

variable {p f : ℕ} [Fact p.Prime]

theorem phanB3Std_of_check (h7 : p ^ f = 7 → Std.Q7.q7MuCheck = true) :
    PhanB3StdSimplyTwoConnected p f :=
  phanB3Std_of_q7 fun h => q7Residual_of_check (h7 h)

end CFSG.ClassicalInvolution.PhanB3.S
