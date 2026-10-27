module

public import CFSG.ClassicalInvolution.Q3.Q3SWCheck
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.ComponentClassification.J2Cover CFSG.Monster.B.Co2.Native

@[expose] def j2WitnessG₁ : Array ℕ :=
  compA 315 (compA 315 cent2AStrong[0]! cent2AStrong[1]!)
    (compA 315 cent2AStrong[0]! cent2AStrong[1]!)

@[expose] def j2WitnessG₂ : Array ℕ :=
  compA 315 (compA 315 cent2AStrong[1]! cent2AStrong[0]!)
    (compA 315 cent2AStrong[1]! cent2AStrong[0]!)

@[expose] def j2WitnessCheck : Bool := witnessCheckA 315 j2WitnessG₁ j2WitnessG₂ twoAArr

end CFSG.ClassicalInvolution.Q3
