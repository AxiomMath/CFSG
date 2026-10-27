module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J2Data
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.LargeExtraspecial

open CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.J2Cover
  CFSG.ClassicalInvolution.J2Data

namespace AS35W

@[expose] def j2Word : List Bool :=
  [true, true, false, true, false, true, true, false, true, false, true, true, false, true,
    false, true, false, true, true, false, true, false, true, true, false, true, false, true]

@[expose] def j2CArr : Array Nat :=
  (j2Word.map fun b => if b then autStrong[1]! else autStrong[0]!).foldr (compA 315) (idA 315)

@[expose] def j2ConjCheck : Bool :=
  eqA 315 (compA 315 j2CArr twoAArr) (compA 315 uStrong[0]! j2CArr) &&
    !eqA 315 uStrong[0]! twoAArr

end AS35W

end CFSG.LargeExtraspecial
