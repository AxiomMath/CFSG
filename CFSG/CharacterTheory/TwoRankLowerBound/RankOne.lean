module

public import CFSG.CharacterTheory.TwoRankLowerBound.CommutingInvolutions
public import CFSG.CharacterTheory.TwoRankLowerBound.RankTransport

public section

open CFSG.Open

namespace CFSG.TwoRankLowerBound.Helpers

theorem exists_central_involution_of_two_group (G : Type*) [Group G] [Finite G]
    [Nontrivial G] (htwogroup : IsPGroup 2 G) :
    ∃ involution : G, orderOf involution = 2 ∧ involution ∈ Subgroup.center G := by
  have := htwogroup.center_nontrivial
  have hcenter : IsPGroup 2 (Subgroup.center G) := htwogroup.to_subgroup _
  have hcardne : Nat.card (Subgroup.center G) ≠ 1 := by
    intro hone
    have hsubsingleton := (Nat.card_eq_one_iff_unique.mp hone).1
    obtain ⟨first, second, hne⟩ := exists_pair_ne (Subgroup.center G)
    exact hne (hsubsingleton.elim first second)
  obtain hcard | hdivides := hcenter.card_eq_or_dvd
  · exact False.elim (hcardne hcard)
  · obtain ⟨involution, horder⟩ := exists_prime_orderOf_dvd_card' 2 hdivides
    exact ⟨involution, (Subgroup.orderOf_coe involution).trans horder,
      involution.property⟩

theorem exists_unique_involution_of_rank_one_two_group (G : Type*) [Group G] [Finite G]
    [Nontrivial G] (htwogroup : IsPGroup 2 G) (hrank : twoRank G ≤ 1) :
    ∃ involution : G, orderOf involution = 2 ∧
      ∀ other : G, orderOf other = 2 → other = involution := by
  obtain ⟨involution, horder, hcentral⟩ := exists_central_involution_of_two_group G htwogroup
  refine ⟨involution, horder, ?_⟩
  intro other hother
  apply commuting_involutions_eq_of_twoRank_le_one G hrank other involution hother horder
  exact Subgroup.mem_center_iff.mp hcentral other

theorem exists_unique_involution_of_rank_one_sylow (G : Type*) [Group G] [Finite G]
    (heven : Even (Nat.card G)) (hrank : twoRank G ≤ 1) (sylow : Sylow 2 G) :
    ∃ involution : G, involution ∈ sylow ∧ orderOf involution = 2 ∧
      ∀ other : G, other ∈ sylow → orderOf other = 2 → other = involution := by
  have : Nontrivial (sylow : Subgroup G) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr
      (sylow.ne_bot_of_dvd_card (even_iff_two_dvd.mp heven))
  obtain ⟨involution, horder, hunique⟩ :=
    exists_unique_involution_of_rank_one_two_group (sylow : Subgroup G)
      sylow.isPGroup' ((twoRank_subgroup_le _).trans hrank)
  refine ⟨involution, involution.property,
    (Subgroup.orderOf_coe involution).trans horder, ?_⟩
  intro other hmember hother
  have hequal := hunique ⟨other, hmember⟩
    ((Subgroup.orderOf_coe ⟨other, hmember⟩).symm.trans hother)
  exact congrArg Subtype.val hequal

end CFSG.TwoRankLowerBound.Helpers
