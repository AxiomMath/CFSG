module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddPrimeNormalizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeTransport

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow

variable {G : Type*} [Group G] [Finite G]

theorem point_subgroup_full_class_card_odd
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G)) :
    Odd (Nat.card (conjugacyWithin H z)) := by
  obtain ⟨g, hgH⟩ : ∃ g : G, g ∉ H := by
    by_contra hnone
    apply h.proper
    apply top_unique
    intro g _
    by_contra hgH
    exact hnone ⟨g, hgH⟩
  let beta := rightCosetMk H g
  have hbeta : beta ≠ rightCosetMk H 1 := by
    intro heq
    have hf : pointRightCosetMul H (rightCosetMk H 1) g = rightCosetMk H 1 := by
      rw [pointRightCosetMul_eq_translate, rightCosetTranslate_mk, one_mul]
      exact heq
    exact hgH ((point_right_base_fixed_iff H g).mp hf)
  have hc := (involution_point_uniform_pair_flips h beta hbeta).1
  have : Nonempty (conjugacyWithin H z) := (conjugacyWithin_nonempty H z).to_subtype
  have hnonzero : Nat.card (rightPairFlipFiber H z beta) ≠ 0 := by
    rw [hc]
    exact Nat.card_pos.ne'
  have : Nonempty (rightPairFlipFiber H z beta) := (Nat.card_ne_zero.mp hnonzero).1
  let t := (Classical.choice this : rightPairFlipFiber H z beta)
  rw [← hc, pair_flip_fiber_eq_odd_class h S hzS hzcenter hbeta t.property]
  exact conjugacyWithin_card_odd _ (pairOddCore_odd H beta) t

theorem two_full_motion_has_fixed_point
    {H M : Subgroup G} {z s : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hs : s ∈ involutionPointClass z)
    (hmotion : Nat.card (conjugacyWithin M s) =
      2 ^ (Nat.card (conjugacyWithin H z)).factorization 2) :
    ∃ a ∈ pointFixedSet H M, pointRightCosetMul H a s = a := by
  have hmOdd := point_subgroup_full_class_card_odd h S hzS hzcenter
  rw [Nat.factorization_eq_zero_of_not_dvd hmOdd.not_two_dvd_nat, pow_zero] at hmotion
  exact class_centralizer_has_pointFixedSet_point h hs
    (centralizes_of_conjugacyWithin_card_one M s hmotion)

theorem no_fixed_point_odd_normalizer_full_class
    {H M : Subgroup G} {z s : G} (h : InvolutionPointLocalEmbedding H z)
    (p : ℕ) (hp : p.Prime) (hodd : Odd p) (hM : IsPGroup p M)
    (hs : s ∈ involutionPointClass z)
    (hsM : s ∈ Subgroup.normalizer (M : Set G))
    (hno : ∀ a ∈ pointFixedSet H M, pointRightCosetMul H a s ≠ a) :
    let N := Subgroup.normalizer (M : Set G)
    let sN : N := ⟨s, hsM⟩
    involutionPointClass z ∩ (N : Set G) = conjugacyWithin N s ∧
      QuotientGroup.mk' (CFSG.oddCore N) sN ∈ Subgroup.center (N ⧸ CFSG.oddCore N) ∧
      ∀ r ∈ conjugacyWithin N s,
        (∀ a ∈ pointFixedSet H M, pointRightCosetMul H a r ≠ a) ∧
        Nat.card (conjugacyWithin M r) = Nat.card (conjugacyWithin M s) := by
  have huniq := ((involution_point_unique_containment_action
    h.distinguished_mem h.distinguished_order).2 h.unique_containment).2.1
  obtain ⟨y, hy, _⟩ := huniq s hs
  have hnot : ¬ M ≤ rightCosetStabilizer H y := by
    intro hMY
    exact hno y ((mem_pointFixedSet_iff H M y).mpr hMY) hy
  have hY := local_point_datum_at_class_fixed_point h hs y hy
  have hclass := pointClass_eq_of_mem hs
  have hfull := CFSG.ProperTwoGeneratedCore.local_involution_point_odd_prime_normalizer_isolation
    hY p hp hodd M hM hsM hnot
  refine ⟨?_, hfull.2.2.2.1, ?_⟩
  · rw [hclass] at hfull
    exact hfull.2.2.1
  · rintro r ⟨n, rfl⟩
    exact ⟨normalizer_conjugate_no_pointFixedSet_fixed hno n,
      conjugacyWithin_card_normalizer_conjugate M s n⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
