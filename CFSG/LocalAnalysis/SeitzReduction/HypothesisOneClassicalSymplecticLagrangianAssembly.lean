module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalSymplecticLagrangian
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalSymplecticShear
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalSymplectic

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 (HypothesisOne)

section Model

variable {r : ℕ} {K : Type} [Field K]

theorem involutionCriterion_spInner_of_eq_orthogonal {f : ℕ} (hr : 3 ≤ r)
    (hK : Nat.card K = 2 ^ f) :
    ∀ s : StatedSp r K, s * s = 1 → s ≠ 1 →
      displacement s = (pairedSympForm K r).orthogonal (displacement s) →
      InvolutionCriterion (spInner r K s) := by
  intro s hs _ hW
  have hf := one_le_of_nontrivial_of_natCard_eq_two_pow hK
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  exact involutionCriterion_spInner_of_eq hr hs hW

theorem hypothesisOne_statedSp_of_ne {f : ℕ} (hr : 3 ≤ r) (hK : Nat.card K = 2 ^ f)
    (hne : ∀ s : StatedSp r K, s * s = 1 → s ≠ 1 →
      displacement s ≠ (pairedSympForm K r).orthogonal (displacement s) →
      InvolutionCriterion (spInner r K s)) :
    HypothesisOne (StatedProj (StatedSp r K)) :=
  hypothesisOne_statedSp hr hK hne (involutionCriterion_spInner_of_eq_orthogonal hr hK)

theorem hypothesisOne_statedSp_of_three_le {f : ℕ} (hr : 3 ≤ r) (hK : Nat.card K = 2 ^ f) :
    HypothesisOne (StatedProj (StatedSp r K)) := by
  have hf := one_le_of_nontrivial_of_natCard_eq_two_pow hK
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  exact hypothesisOne_statedSp_of_ne hr hK fun _ hs hs1 hW =>
    involutionCriterion_spInner_of_ne hr hs hs1 hW

end Model

theorem forall_involutionCriterion_spInner_of_eq_orthogonal {r f : ℕ} (hr : 3 ≤ r) :
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f →
      ∀ s : StatedSp r K, s * s = 1 → s ≠ 1 →
        displacement s = (pairedSympForm K r).orthogonal (displacement s) →
        InvolutionCriterion (spInner r K s) :=
  fun _ _ _ _ _ _ hs _ hW => involutionCriterion_spInner_of_eq hr hs hW

theorem hypothesisOne_of_lieModel_PSp_of_ne {Y : Type} [Group Y] {r f : ℕ} (hr : 3 ≤ r)
    (hne : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f →
      ∀ s : StatedSp r K, s * s = 1 → s ≠ 1 →
        displacement s ≠ (pairedSympForm K r).orthogonal (displacement s) →
        InvolutionCriterion (spInner r K s))
    (h : CFSG.Blueprint.LieModel Y .PSp r 2 f) : HypothesisOne Y :=
  hypothesisOne_of_lieModel_PSp hr hne (forall_involutionCriterion_spInner_of_eq_orthogonal hr) h

theorem hypothesisOne_of_lieModel_PSp_of_three_le {Y : Type} [Group Y] {r f : ℕ} (hr : 3 ≤ r)
    (h : CFSG.Blueprint.LieModel Y .PSp r 2 f) : HypothesisOne Y :=
  hypothesisOne_of_lieModel_PSp_of_ne hr
    (fun _ _ _ _ _ _ hs hs1 hW => involutionCriterion_spInner_of_ne hr hs hs1 hW) h

end CFSG.SeitzReduction
