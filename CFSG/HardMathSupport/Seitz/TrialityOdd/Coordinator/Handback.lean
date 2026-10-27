module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Bridge
public import CFSG.LieType.SeitzGeneration.ExcAnisotropicTriality

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator

open TauCeti CFSG.LieType.SeitzGeneration

theorem seitzExcAnisotropicForAt_trialityThree_odd_of_model (h3 : InnerModelGen (· = 3)) :
    SeitzExcAnisotropicForAt IsTrialityIndex
      (fun d p => PrimeRange.three d p ∧ ∃ q : PrimePower, d = .trialityD4 q ∧ q.p ≠ 2) :=
  seitzExcAnisotropicForAt_of_innerModelGen h3

theorem seitzExcAnisotropicForAt_trialityOdd_handback (h3 : InnerModelGen (· = 3))
    (h5 : SeitzExcAnisotropicTrialityOdd) :
    SeitzExcAnisotropicForAt IsTrialityIndex
      (fun d _ => ∃ q : PrimePower, d = .trialityD4 q ∧ q.p ≠ 2) :=
  SeitzExcAnisotropicForAt.union
    (fun _ _ hp hp2 hq => (PrimeRange.eq_three_or_five_le hp hp2).imp (fun h => ⟨h, hq⟩)
      fun h => ⟨h, hq⟩)
    (seitzExcAnisotropicForAt_trialityThree_odd_of_model h3) h5

end CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
