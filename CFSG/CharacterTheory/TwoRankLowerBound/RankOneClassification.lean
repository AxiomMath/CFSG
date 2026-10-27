module

public import CFSG.CharacterTheory.TwoRankLowerBound.CyclicIndexTwo
public import CFSG.CharacterTheory.TwoRankLowerBound.QuaternionNormalForm

public section

open CFSG.Open

namespace CFSG.TwoRankLowerBound.Helpers

theorem rank_one_two_group_cyclic_or_quaternion (G : Type*) [Group G] [Finite G]
    (htwogroup : IsPGroup 2 G) (hrank : twoRank G ≤ 1) :
    IsCyclic G ∨ ∃ exponent : ℕ, 3 ≤ exponent ∧
      Nonempty (G ≃* QuaternionGroup (2 ^ (exponent - 2))) := by
  classical
  by_cases hab : IsMulCommutative G
  · left
    have := hab
    let : CommGroup G := Group.commGroupOfCenterEqTop Subgroup.center_eq_top
    exact abelian_rank_one_two_group_isCyclic G htwogroup hrank
  · right
    have hnonabelian := isMulCommutative_iff.not.mp hab
    push Not at hnonabelian
    have hcentertwo := center_card_eq_two_of_nonabelian_rank_one_two_group G htwogroup hrank
      hnonabelian
    obtain ⟨normal, hnormal, hnormalcyclic, hfour, hcyclic, hindex⟩ :=
      exists_cyclic_index_two_subgroup_of_nonabelian_rank_one_two_group G htwogroup hrank
        hnonabelian
    have := hnormalcyclic
    have := hcyclic
    let cyclic := Subgroup.centralizer (normal : Set G)
    have hcenterle : Subgroup.center G ≤ cyclic := Subgroup.center_le_centralizer _
    obtain ⟨outside, houtsideorder, houtside⟩ :=
      exists_order_four_outside_centralizer_of_cyclic_four_subgroup G htwogroup hrank
        normal hfour hcentertwo
    obtain ⟨power, hpower⟩ := (htwogroup.to_subgroup cyclic).exists_card_eq
    have hpowerge : 2 ≤ power := by
      have hle := Subgroup.card_le_of_le (Subgroup.le_centralizer normal)
      rw [hfour, hpower] at hle
      by_contra hnot
      have hsmall : power ≤ 1 := by omega
      interval_cases power <;> norm_num at hle
    obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : power ≠ 0)
    have hcard : Nat.card cyclic = 2 * 2 ^ previous := by rw [hpower, pow_succ]; omega
    obtain ⟨isomorphism⟩ := quaternion_normal_form_isomorphism_of_cyclic_index_two G
      htwogroup hrank cyclic hindex hcenterle hcentertwo (2 ^ previous) (by positivity)
      hcard outside houtside houtsideorder
    refine ⟨previous + 2, by omega, ?_⟩
    have hexponent : previous + 2 - 2 = previous := by omega
    rw [hexponent]
    exact ⟨isomorphism.symm⟩

theorem sylow_two_quaternion_of_perfect_rank_one (G : Type*) [Group G] [Finite G]
    [Group.IsPerfect G] (heven : Even (Nat.card G)) (hrank : twoRank G ≤ 1)
    (sylow : Sylow 2 G) :
    ∃ exponent : ℕ, 3 ≤ exponent ∧
      Nonempty ((sylow : Subgroup G) ≃* QuaternionGroup (2 ^ (exponent - 2))) := by
  obtain hcyclic | hquaternion := rank_one_two_group_cyclic_or_quaternion
    (sylow : Subgroup G) sylow.isPGroup' ((twoRank_subgroup_le _).trans hrank)
  · exact False.elim (sylow_two_not_isCyclic_of_perfect G heven sylow hcyclic)
  · exact hquaternion

theorem sylow_two_quaternion_of_nonabelian_simple_rank_one (G : Type*)
    [Group G] [Finite G] [IsSimpleGroup G]
    (hnonabelian : ∃ left right : G, left * right ≠ right * left)
    (heven : Even (Nat.card G)) (hrank : twoRank G ≤ 1) (sylow : Sylow 2 G) :
    ∃ exponent : ℕ, 3 ≤ exponent ∧
      Nonempty ((sylow : Subgroup G) ≃* QuaternionGroup (2 ^ (exponent - 2))) := by
  have := perfect_of_nonabelian_simple G hnonabelian
  exact sylow_two_quaternion_of_perfect_rank_one G heven hrank sylow

end CFSG.TwoRankLowerBound.Helpers
