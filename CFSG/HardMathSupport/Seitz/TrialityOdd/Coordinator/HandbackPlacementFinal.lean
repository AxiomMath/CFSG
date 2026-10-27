module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6ThreeLiftProved
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWCoreThree

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator

open TauCeti CFSG.LieType.SeitzGeneration

theorem seitzExcAnisotropicForAt_trialityOdd_handback_of_placements
    (hS : ∀ r, 5 ≤ r → Phi6PlacementSome r) (h3 : ∀ r, 5 ≤ r → Inner.Phi6PlacementSomeThree r) :
    SeitzExcAnisotropicForAt IsTrialityIndex
      (fun d _ => ∃ q : PrimePower, d = .trialityD4 q ∧ q.p ≠ 2) :=
  seitzExcAnisotropicForAt_trialityOdd_handback_of_coreW' fun r hr5 =>
    Inner.phi6CoreW_of_placementSome hr5 (hS r hr5) (h3 r hr5)

end CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
