module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoRankTwo

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore
open CFSG.SignalizerFunctor.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem odd_subgroup_le_normalizer_of_commuting_involutions (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (z w : G) (hzQ : z ∈ Q) (hwQ : w ∈ Q)
    (hz : orderOf z = 2) (hw : orderOf w = 2) (hne : z ≠ w) (hcomm : Commute z w)
    (X : Subgroup G) (hXodd : Odd (Nat.card X))
    (hnormalizes : Subgroup.zpowers z ⊔ Subgroup.zpowers w ≤
      Subgroup.normalizer (X : Set G)) : X ≤ Subgroup.normalizer (Q : Set G) := by
  let A := Subgroup.zpowers z ⊔ Subgroup.zpowers w
  obtain ⟨hA, hAcard, hcases⟩ :=
    commuting_distinct_involutions_four_group hz hw hcomm hne.symm
  have hproductneq : z * w ≠ 1 := by
    intro heq
    exact hne ((mul_eq_one_iff_eq_inv.mp heq).trans (inv_eq_self_of_orderOf_eq_two hw))
  have hproductorder : orderOf (z * w) = 2 := by
    apply orderOf_eq_prime_iff.mpr
    refine ⟨?_, hproductneq⟩
    rw [hcomm.mul_pow]
    have hzsq : z ^ 2 = 1 := by simpa only [hz] using pow_orderOf_eq_one z
    have hwsq : w ^ 2 = 1 := by simpa only [hw] using pow_orderOf_eq_one w
    rw [hzsq, hwsq, one_mul]
  have hproductcentralizer :=
    involution_centralizer_le_normalizer Q hodd (z * w) (Q.mul_mem hzQ hwQ) hproductorder
  rw [← elementary_abelian_centralizer_generation 2 1 Nat.prime_two A X hA
    (by simpa using hAcard.ge) hnormalizes (Nat.coprime_two_left.mpr hXodd)]
  apply iSup_le
  intro U
  apply iSup_le
  intro hU
  have hUcard : Nat.card U = 2 := by simpa using hU.2
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := U) 2
    (by simp only [hUcard, dvd_refl])
  have haG : orderOf (a : G) = 2 := (Subgroup.orderOf_coe a).trans ha
  have haneq : (a : G) ≠ 1 := by
    intro heq
    simp [heq] at haG
  have haA : (a : G) ∈ A := hU.1 a.property
  have hcentralizer : Subgroup.centralizer (U : Set G) ≤
      Subgroup.centralizer ({(a : G)} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr a.property)
  apply (inf_le_right.trans hcentralizer).trans
  rcases hcases (a : G) haA with hone | haz | haw | hproduct
  · exact False.elim (haneq hone)
  · rw [haz]
    exact involution_centralizer_le_normalizer Q hodd z hzQ hz
  · rw [haw]
    exact involution_centralizer_le_normalizer Q hodd w hwQ hw
  · rw [hproduct]
    exact hproductcentralizer

theorem odd_normal_subgroup_le_normalizer_of_commuting_involutions (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (z w : G) (hzQ : z ∈ Q) (hwQ : w ∈ Q)
    (hz : orderOf z = 2) (hw : orderOf w = 2) (hne : z ≠ w) (hcomm : Commute z w)
    (X : Subgroup G) [X.Normal] (hXodd : Odd (Nat.card X)) :
    X ≤ Subgroup.normalizer (Q : Set G) :=
  odd_subgroup_le_normalizer_of_commuting_involutions Q hodd z w hzQ hwQ hz hw hne hcomm
    X hXodd (by rw [Subgroup.normalizer_eq_top]; exact le_top)

theorem oddCore_le_normalizer_of_rank_two_Q (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hrank : 2 ≤ twoRank Q) :
    oddCore G ≤ Subgroup.normalizer (Q : Set G) := by
  obtain ⟨z, w, hzQ, hwQ, hz, hw, hne, hcomm⟩ :=
    rank_two_Q_exists_commuting_involutions Q hrank
  exact odd_normal_subgroup_le_normalizer_of_commuting_involutions Q hodd z w
    hzQ hwQ hz hw hne hcomm (oddCore G) (CFSG.ComponentClassification.OddCore.odd_card G)

end CFSG.ComponentClassification.AschbacherTightEmbedding
