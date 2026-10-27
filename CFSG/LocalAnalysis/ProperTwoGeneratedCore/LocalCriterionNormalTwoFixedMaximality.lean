module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedCommutation
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixed

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow

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

theorem full_motion_fixed_card_le_two
    {H Q P : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hQH : Q ≤ H) (hQnormal : (Q.subgroupOf H).Normal)
    (hQtwo : IsPGroup 2 Q) (hzQ : z ∈ Q)
    (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hpart : 1 < p ^ (Nat.card (conjugacyWithin H z)).factorization p)
    (hP : IsPGroup p P) (r : G) (hr : r ∈ involutionPointClass z)
    (hrP : r ∈ Subgroup.normalizer (P : Set G))
    (hmotion : Nat.card (conjugacyWithin P r) =
      p ^ (Nat.card (conjugacyWithin H z)).factorization p) :
    Nat.card (pointFixedSet H P) ≤ 2 := by
  by_contra hlarge
  obtain ⟨M, _, hM, hMfixed, hmax, s, hs, hsM, hsmotion⟩ :=
    exists_maximal_full_motion H P z p hP (by omega) r hr hrP hmotion
  obtain ⟨gamma, hgamma, hsfixed⟩ :=
    local_involution_point_maximal_prime_fixed_point H z h S hzS hzcenter
      p hp M hM s hs hsM hMfixed hsmotion hmax
  obtain ⟨k, hk⟩ := isPGroup_iff_card_dvd_pow.mp hM
  have hModd : Odd (Nat.card M) := (show Odd (p ^ k) from hodd.pow).of_dvd_nat hk
  have hcentral := odd_subgroup_at_class_fixed_point_centralizes
    h hQH hQnormal hQtwo hzQ hModd hs hsM gamma hgamma hsfixed
  have hone : Nat.card (conjugacyWithin M s) = 1 := by
    rw [conjugacyWithin_card_eq_centralizer_index]
    change (Subgroup.centralizer ({s} : Set G)).relIndex M = 1
    exact Subgroup.relIndex_eq_one.mpr hcentral
  rw [hone] at hsmotion
  omega

end CFSG.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixed
