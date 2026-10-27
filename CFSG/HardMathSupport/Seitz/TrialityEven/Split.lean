module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.TrialityThreeAssembly

public section

namespace CFSG.HardMathSupport.Seitz.TrialityEven

open TauCeti CFSG.LieType.SeitzGeneration
open CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator (SeitzExcAnisotropicTrialityEvenThree)

@[expose] def TrialityTwoThreePlanes : Prop :=
  SeitzExcAnisotropicForAt IsTrialityIndex fun d p =>
    p = 3 ∧ ∃ q : PrimePower, d = .trialityD4 q ∧ q.p = 2 ∧ q.exponent = 1

@[expose] def SeitzExcAnisotropicTrialityEvenThreeGe : Prop :=
  SeitzExcAnisotropicForAt IsTrialityIndex fun d p =>
    p = 3 ∧ ∃ q : PrimePower, d = .trialityD4 q ∧ q.p = 2 ∧ 2 ≤ q.exponent

theorem seitzExcAnisotropicTrialityEvenThree_of_split (h2 : TrialityTwoThreePlanes)
    (h4 : SeitzExcAnisotropicTrialityEvenThreeGe) : SeitzExcAnisotropicTrialityEvenThree :=
  SeitzExcAnisotropicForAt.union
    (fun _ _ _ _ ⟨hp, q, hd, hq⟩ => by
      have hpos := q.exponent_pos
      by_cases h : q.exponent = 1
      · exact Or.inl ⟨hp, q, hd, hq, h⟩
      · exact Or.inr ⟨hp, q, hd, hq, by omega⟩)
    h2 h4

end CFSG.HardMathSupport.Seitz.TrialityEven
