module

public import CFSG.CharacterTheory.TwoRankLowerBound.CentralQuotientPair

public section

open CFSG.Open

namespace CFSG.TwoRankLowerBound.Helpers

theorem involution_mem_center_of_rank_one_two_group (G : Type*) [Group G] [Finite G]
    (htwogroup : IsPGroup 2 G) (hrank : twoRank G ≤ 1) (involution : G)
    (horder : orderOf involution = 2) : involution ∈ Subgroup.center G := by
  have hne : involution ≠ 1 := (orderOf_eq_prime_iff.mp horder).2
  have : Nontrivial G := nontrivial_of_ne involution 1 hne
  obtain ⟨central, hcentralorder, hcentral⟩ := exists_central_involution_of_two_group G htwogroup
  have hequal := commuting_involutions_eq_of_twoRank_le_one G hrank involution central
    horder hcentralorder (Subgroup.mem_center_iff.mp hcentral involution)
  rw [hequal]
  exact hcentral

theorem exists_order_four_power_of_noncentral_element (G : Type*) [Group G] [Finite G]
    (htwogroup : IsPGroup 2 G) (hrank : twoRank G ≤ 1)
    (hcentertwo : Nat.card (Subgroup.center G) = 2) (element : G)
    (hnoncentral : element ∉ Subgroup.center G) :
    ∃ exponent : ℕ, orderOf (element ^ exponent) = 4 := by
  have hordergt := center_card_lt_orderOf_of_rank_one_two_group G htwogroup hrank element
    hnoncentral
  rw [hcentertwo] at hordergt
  obtain ⟨power, hpower⟩ := htwogroup.exists_orderOf_eq_pow element
  have hpowerge : 2 ≤ power := by
    by_contra hnot
    have hle : power ≤ 1 := by omega
    interval_cases power <;> norm_num [hpower] at hordergt
  refine ⟨orderOf element / 4, orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos element)) ?_⟩
  rw [hpower]
  simpa using Nat.pow_dvd_pow 2 hpowerge

theorem exists_order_four_outside_centralizer_of_cyclic_four_subgroup (G : Type*)
    [Group G] [Finite G] (htwogroup : IsPGroup 2 G) (hrank : twoRank G ≤ 1)
    (normal : Subgroup G) [IsCyclic normal] (hfour : Nat.card normal = 4)
    (hcentertwo : Nat.card (Subgroup.center G) = 2) :
    ∃ element : G, orderOf element = 4 ∧
      element ∉ Subgroup.centralizer (normal : Set G) := by
  classical
  by_contra hnot
  push Not at hnot
  obtain ⟨subgroupGenerator, hsubgroupGenerator⟩ :=
    isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic normal)
  let generator : G := subgroupGenerator
  have hgenerator : Subgroup.zpowers generator = normal := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem subgroupGenerator.property)
    rw [Nat.card_zpowers, Subgroup.orderOf_coe subgroupGenerator, hsubgroupGenerator]
  have hgeneratororder : orderOf generator = 4 := by
    rw [← Nat.card_zpowers generator, hgenerator, hfour]
  have hnormalcenter : normal ≤ Subgroup.center G := by
    intro member hmember
    apply Subgroup.mem_center_iff.mpr
    intro element
    by_cases hcentral : element ∈ Subgroup.center G
    · exact (Subgroup.mem_center_iff.mp hcentral member).symm
    · obtain ⟨exponent, hpowerorder⟩ := exists_order_four_power_of_noncentral_element G
        htwogroup hrank hcentertwo element hcentral
      have hpowercentralizer := hnot (element ^ exponent) hpowerorder
      have hgeneratornormal : generator ∈ normal := by
        rw [← hgenerator]
        exact Subgroup.mem_zpowers generator
      have hcommute : Commute generator (element ^ exponent) :=
        Subgroup.mem_centralizer_iff.mp hpowercentralizer generator hgeneratornormal
      have hpowers := commuting_elements_same_order_eq_zpowers_of_rank_one_two_group
        G htwogroup hrank generator (element ^ exponent) hcommute
        (hgeneratororder.trans hpowerorder.symm)
      have hmemberpower : member ∈ Subgroup.zpowers (element ^ exponent) := by
        rw [← hpowers, hgenerator]
        exact hmember
      obtain ⟨integerPower, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmemberpower
      exact ((Commute.refl element).pow_right exponent).zpow_right integerPower
  have hcardle := Subgroup.card_le_of_le hnormalcenter
  rw [hfour, hcentertwo] at hcardle
  omega

end CFSG.TwoRankLowerBound.Helpers
