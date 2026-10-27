module

public import CFSG.ClassicalInvolution.LBalance.Proof
public import CFSG.ClassicalInvolution.LBalance.Glauberman

public section

namespace CFSG.ClassicalInvolution

theorem l2PrimeBalance : L2PrimeBalance :=
  l2PrimeBalance_of_glauberman glaubermanSylowFixingSolvable

end CFSG.ClassicalInvolution
