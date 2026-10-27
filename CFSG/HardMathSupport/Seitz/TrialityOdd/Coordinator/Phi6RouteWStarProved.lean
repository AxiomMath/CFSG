module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6RouteWStar
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.TwoTorusSL2
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.AnisotropicGL2

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator

open TauCeti CFSG.LieType.SeitzGeneration

theorem twoTorusGenOdd : TwoTorusGenOdd :=
  fun _ _ _ hK h27 _ _ hE hD2 hDs hDE =>
    CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.closure_centralizers_eq_top hK h27 hE hD2 hDs hDE

theorem anisotropicOfPowOdd : AnisotropicOfPowOdd :=
  fun _ _ _ _ hr hr2 hrK hr1 _ hpow hns a =>
    CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.charpoly_eval_ne_zero_of_pow_scalar hr hr2 hrK
      hr1 hpow hns a


theorem phiPlaneGenAt_neg_of_coreW {r : ℕ} (hr5 : 5 ≤ r) (h : Phi6CoreW r) :
    PhiPlaneGenAt (-1) r :=
  phiPlaneGenAt_neg_of_core twoTorusGenOdd anisotropicOfPowOdd hr5 h

theorem seitzExcAnisotropicTrialityOdd_of_coreW (h : ∀ r, 5 ≤ r → Phi6CoreW r) :
    SeitzExcAnisotropicTrialityOdd :=
  seitzExcAnisotropicTrialityOdd_of_core twoTorusGenOdd anisotropicOfPowOdd h

theorem seitzExcAnisotropicForAt_trialityOdd_handback_of_coreW (h : ∀ r, 5 ≤ r → Phi6CoreW r)
    (h63 : PhiFramePlaneGenAt (-1) 3) :
    SeitzExcAnisotropicForAt IsTrialityIndex
      (fun d _ => ∃ q : PrimePower, d = .trialityD4 q ∧ q.p ≠ 2) :=
  seitzExcAnisotropicForAt_trialityOdd_handback_of_core twoTorusGenOdd anisotropicOfPowOdd h h63

end CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
