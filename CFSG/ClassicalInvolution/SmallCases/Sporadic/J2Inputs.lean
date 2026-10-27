module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J2Data
public import CFSG.Sporadic.Schreier.RuEnum
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckInputs

public section

namespace CFSG.ClassicalInvolution
namespace J2Proof

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.ComponentClassification.J2Cover CFSG.Sporadic.RuSchreier CFSG.ClassicalInvolution.J2Data

@[expose] def cent2ALevels : Array Level := rawLevels 315 cent2AStrong cent2ABase

@[expose] def cent2BLevels : Array Level := rawLevels 315 cent2BStrong cent2BBase

@[expose] def uLevels : Array Level := rawLevels 315 uStrong uBase

@[expose] def nLevels : Array Level := rawLevels 315 nStrong nBase

@[expose] def selfCentTest (t : Array ℕ) : Bool :=
  !((List.range 4).all fun i => commA t uStrong[i]!) || siftA 315 uLevels uBase 0 t

end J2Proof
end CFSG.ClassicalInvolution
