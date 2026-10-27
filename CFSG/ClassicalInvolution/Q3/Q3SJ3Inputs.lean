module

public import CFSG.ClassicalInvolution.Q3.Q3SWCheck
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3Data

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.ClassicalInvolution.J3Data CFSG.Monster.B.Co2.Native

@[expose] def j3WitnessG₁ : Array ℕ := compA 20520 kStrong[0]! kStrong[1]!

@[expose] def j3WitnessG₂ : Array ℕ :=
  compA 20520 kStrong[1]! (compA 20520 kStrong[0]! (compA 20520 kStrong[0]!
    (compA 20520 kStrong[1]! (compA 20520 kStrong[1]! (compA 20520 kStrong[0]!
      (compA 20520 kStrong[1]! kStrong[0]!))))))

@[expose] def j3WitnessCheck : Bool := witnessCheckA 20520 j3WitnessG₁ j3WitnessG₂ abArr[0]!

end CFSG.ClassicalInvolution.Q3
