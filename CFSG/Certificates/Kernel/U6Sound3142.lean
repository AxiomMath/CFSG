
module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Sylow
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.KC.U6

@[expose] def decZ (c : Nat) : Int := if c % 2 = 0 then Int.ofNat (c / 2 + 1) else Int.negSucc (c / 2)

end CFSG.KC.U6

end
