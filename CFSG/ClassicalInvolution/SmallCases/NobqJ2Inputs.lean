module

public import CFSG.ClassicalInvolution.SmallCases.NobqArr
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J2Inputs

public section

namespace CFSG.ClassicalInvolution.Nobq

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.ComponentClassification.J2Cover CFSG.Sporadic.RuSchreier CFSG.ClassicalInvolution.J2Data
  CFSG.ClassicalInvolution.J2Proof

@[expose] def cent2AWit : List (Array ℕ) :=
  closureA 315 [cent2AStrong[0]!, cent2AStrong[1]!] 4

end CFSG.ClassicalInvolution.Nobq
