module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeMaximality
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeAction

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

variable {G : Type*} [Group G] [Finite G]

theorem maximal_prime_motion_fixed_point
    {H M : Subgroup G} {z s : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (p : ℕ) (hp : p.Prime) (hM : IsPGroup p M)
    (hs : s ∈ involutionPointClass z)
    (hsM : s ∈ Subgroup.normalizer (M : Set G))
    (hfixed : 3 ≤ Nat.card (pointFixedSet H M))
    (hmotion : Nat.card (conjugacyWithin M s) =
      p ^ (Nat.card (conjugacyWithin H z)).factorization p)
    (hmax : IsMaximalPrimeMotion H z p M) :
    ∃ a ∈ pointFixedSet H M, pointRightCosetMul H a s = a := by
  rcases hp.eq_two_or_odd' with rfl | hpodd
  · exact two_full_motion_has_fixed_point h S hzS hzcenter hs hmotion
  classical
  by_contra hnot
  have hno : ∀ a ∈ pointFixedSet H M, pointRightCosetMul H a s ≠ a := by
    intro a ha hf
    exact hnot ⟨a, ha, hf⟩
  let N := Subgroup.normalizer (M : Set G)
  let sN : N := ⟨s, hsM⟩
  let Delta := pointFixedSet H M
  let := pointInvariantSetInverseRightAction H N Delta
    (fun n hn a ha => normalizer_preserves_pointFixedSet hn ha)
  obtain ⟨hclass, hcentral, hpropagate⟩ := no_fixed_point_odd_normalizer_full_class
    h p hp hpodd hM hs hsM hno
  have hsOrder : orderOf sN = 2 := (Subgroup.orderOf_coe sN).symm.trans
    (order_two_of_mem_pointClass h.distinguished_order hs)
  have hNclass (r : N) (hr : r ∈ involutionPointClass sN) :
      (r : G) ∈ conjugacyWithin N s := by
    obtain ⟨n, hn⟩ := hr
    exact ⟨n, congrArg Subtype.val hn⟩
  have hNno : ∀ r ∈ involutionPointClass sN, ∀ a : Delta, r • a ≠ a := by
    intro r hr a hf
    have hnoOriginal := (hpropagate (r : G) (hNclass r hr)).1
    have hh := congrArg Subtype.val hf
    change pointRightCosetMul H a.val (r : G)⁻¹ = a.val at hh
    have hrorder : orderOf (r : G) = 2 := (Subgroup.orderOf_coe r).trans
      (order_two_of_mem_pointClass hsOrder hr)
    rw [inv_eq_self_of_orderOf_eq_two hrorder] at hh
    exact hnoOriginal a.val a.property hh
  have hNflip : ∀ a b : Delta, a ≠ b →
      ∃ r ∈ involutionPointClass sN, r • a = b := by
    intro a b hab
    have hval : a.val ≠ b.val := fun heq => hab (Subtype.ext heq)
    obtain ⟨r, ⟨n, hn⟩, hrflip⟩ := maximalPrimeMotion_normalizer_class_pair_flips
      h S hzS hzcenter p hp hpodd hM hs hsM hmotion hmax hno a.val b.val
      a.property b.property hval
    have hrN : r ∈ N := by
      rw [← hn]
      exact N.mul_mem (N.mul_mem (N.inv_mem n.property) hsM) n.property
    let rN : N := ⟨r, hrN⟩
    have hrclass : rN ∈ involutionPointClass sN := by
      refine ⟨n, ?_⟩
      exact Subtype.ext hn
    refine ⟨rN, hrclass, ?_⟩
    apply Subtype.ext
    change pointRightCosetMul H a.val (r : G)⁻¹ = b.val
    have hrorder : orderOf r = 2 := (Subgroup.orderOf_coe rN).trans
      (order_two_of_mem_pointClass hsOrder hrclass)
    rwa [inv_eq_self_of_orderOf_eq_two hrorder]
  have hdegree : Nat.card Delta ≤ 2 :=
    odd_central_involution_class_pair_flips_card_le_two
      (CFSG.oddCore N) (CFSG.ComponentClassification.OddCore.odd_card N)
      sN hsOrder hcentral hNno hNflip
  change Nat.card (pointFixedSet H M) ≤ 2 at hdegree
  omega

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

namespace CFSG.ProperTwoGeneratedCore

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

variable {G : Type*} [Group G] [Finite G]

theorem local_involution_point_maximal_prime_fixed_point
    (H : Subgroup G) (z : G) (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (p : ℕ) (hp : p.Prime) (M : Subgroup G) (hM : IsPGroup p M)
    (s : G) (hs : s ∈ involutionPointClass z)
    (hsM : s ∈ Subgroup.normalizer (M : Set G))
    (hfixed : 3 ≤ Nat.card (pointFixedSet H M))
    (hmotion : Nat.card (conjugacyWithin M s) =
      p ^ (Nat.card (conjugacyWithin H z)).factorization p)
    (hmax : ∀ Q : Subgroup G, IsPGroup p Q → M < Q →
      3 ≤ Nat.card (pointFixedSet H Q) →
      ¬ ∃ r ∈ involutionPointClass z, r ∈ Subgroup.normalizer (Q : Set G) ∧
        Nat.card (conjugacyWithin Q r) =
          p ^ (Nat.card (conjugacyWithin H z)).factorization p) :
    ∃ a ∈ pointFixedSet H M, pointRightCosetMul H a s = a :=
  maximal_prime_motion_fixed_point h S hzS hzcenter p hp hM hs hsM hfixed hmotion hmax

end CFSG.ProperTwoGeneratedCore
