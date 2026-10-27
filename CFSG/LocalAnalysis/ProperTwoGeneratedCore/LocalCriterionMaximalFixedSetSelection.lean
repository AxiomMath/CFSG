module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeMaximality

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSet

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

theorem exists_maximal_full_motion
    (H P : Subgroup G) (z : G) (p : ℕ) (hP : IsPGroup p P)
    (hfixed : 3 ≤ Nat.card (pointFixedSet H P))
    (r : G) (hr : r ∈ involutionPointClass z)
    (hrP : r ∈ Subgroup.normalizer (P : Set G))
    (hmotion : Nat.card (conjugacyWithin P r) =
      p ^ (Nat.card (conjugacyWithin H z)).factorization p) :
    ∃ M : Subgroup G, P ≤ M ∧ IsPGroup p M ∧
      3 ≤ Nat.card (pointFixedSet H M) ∧ IsMaximalPrimeMotion H z p M ∧
      ∃ s ∈ involutionPointClass z, s ∈ Subgroup.normalizer (M : Set G) ∧
        Nat.card (conjugacyWithin M s) =
          p ^ (Nat.card (conjugacyWithin H z)).factorization p := by
  let property : Subgroup G → Prop := fun A => IsPGroup p A ∧
    3 ≤ Nat.card (pointFixedSet H A) ∧
    ∃ s ∈ involutionPointClass z, s ∈ Subgroup.normalizer (A : Set G) ∧
      Nat.card (conjugacyWithin A s) =
        p ^ (Nat.card (conjugacyWithin H z)).factorization p
  obtain ⟨M, hPM, hmax⟩ := Finite.exists_le_maximal
    (show property P from ⟨hP, hfixed, r, hr, hrP, hmotion⟩)
  refine ⟨M, hPM, hmax.1.1, hmax.1.2.1, ?_, hmax.1.2.2⟩
  intro A hA hMA hAfixed hAmotion
  exact (not_le_of_gt hMA) (hmax.2 ⟨hA, hAfixed, hAmotion⟩ hMA.le)

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSet
