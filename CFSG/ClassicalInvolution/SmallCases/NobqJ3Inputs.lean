module

public import CFSG.ClassicalInvolution.SmallCases.NobqArr
public import CFSG.Assembly.Defs
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3CheckInputs
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative

public section

namespace CFSG.ClassicalInvolution.Nobq

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier.Co3.Native CFSG.ClassicalInvolution.J3Data
  CFSG.ComponentClassification.J2Cover CFSG.ClassicalInvolution.J3Proof

@[expose] def kWit : List (Array ℕ) := closureA 20520 [kStrong[0]!, kStrong[1]!] 4

end CFSG.ClassicalInvolution.Nobq
