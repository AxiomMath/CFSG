module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.ThreeQ1
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.ClosingOddProved

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator

open TauCeti CFSG.LieType.SeitzGeneration

theorem phiPlaneGenAt_one_proved {r : ℕ} (hr3 : r ≠ 3) : PhiPlaneGenAt 1 r :=
  phiPlaneGenAt_one_of_closing longTorusClosingOdd_proved hr3

theorem seitzExcAnisotropicTrialityOdd_of_phi6 (h6 : ∀ r, 5 ≤ r → PhiPlaneGenAt (-1) r) :
    SeitzExcAnisotropicTrialityOdd :=
  seitzExcAnisotropicTrialityOdd_of_closing longTorusClosingOdd_proved h6

theorem seitzExcAnisotropicForAt_trialityOdd_handback_of_phi6
    (h6 : ∀ r, 5 ≤ r → PhiPlaneGenAt (-1) r) (h63 : PhiFramePlaneGenAt (-1) 3) :
    SeitzExcAnisotropicForAt IsTrialityIndex
      (fun d _ => ∃ q : PrimePower, d = .trialityD4 q ∧ q.p ≠ 2) :=
  seitzExcAnisotropicForAt_trialityOdd_handback_of_closing' longTorusClosingOdd_proved h6 h63

end CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
