module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.HandbackPlacementFinal
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJPlacement
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreePerX

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator

open TauCeti CFSG.LieType.SeitzGeneration

@[expose] def SeitzExcAnisotropicTrialityEvenThree : Prop :=
  SeitzExcAnisotropicForAt IsTrialityIndex fun d p =>
    p = 3 ∧ ∃ q : PrimePower, d = .trialityD4 q ∧ q.p = 2


theorem seitzExcAnisotropicForAt_trialityOdd_proved :
    SeitzExcAnisotropicForAt IsTrialityIndex
      (fun d _ => ∃ q : PrimePower, d = .trialityD4 q ∧ q.p ≠ 2) :=
  seitzExcAnisotropicForAt_trialityOdd_handback_of_placements
    (fun r hr => Inner.phi6PlacementSome_holds r hr)
    (fun r hr => Inner.phi6PlacementSomeThree_holds r hr)

theorem seitzExcAnisotropicTrialityThree_of_even (h : SeitzExcAnisotropicTrialityEvenThree) :
    SeitzExcAnisotropicTrialityThree := by
  intro d p hp hp2 hpd hex E hE hc ⟨hin, hP, hQ, hr, hn⟩
  obtain ⟨q, hq⟩ := hP
  by_cases h2 : q.p = 2
  · exact h d p hp hp2 hpd hex E hE hc ⟨hin, ⟨q, hq⟩, ⟨hQ, q, hq, h2⟩, hr, hn⟩
  · exact seitzExcAnisotropicForAt_trialityOdd_proved d p hp hp2 hpd hex E hE hc
      ⟨hin, ⟨q, hq⟩, ⟨q, hq, h2⟩, hr, hn⟩

end CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
