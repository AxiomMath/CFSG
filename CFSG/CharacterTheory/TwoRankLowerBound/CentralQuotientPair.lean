module

public import CFSG.CharacterTheory.TwoRankLowerBound.CyclicTwoSubgroups

public section

open CFSG.Open

namespace CFSG.TwoRankLowerBound.Helpers

theorem exists_square_root_in_cyclic_two_subgroup (G : Type*) [Group G] [Finite G]
    (htwogroup : IsPGroup 2 G) (cyclic : Subgroup G) [IsCyclic cyclic]
    (proper : Subgroup G) (hproper : proper < cyclic) (element : G)
    (hmember : element ∈ proper) :
    ∃ root : G, root ∈ cyclic ∧ root ^ 2 = element := by
  let : CommGroup cyclic := IsCyclic.commGroup
  have hne : proper.subgroupOf cyclic ≠ ⊤ := by
    intro hequal
    have hreverse : cyclic ≤ proper := by
      intro member hmember
      have : (⟨member, hmember⟩ : cyclic) ∈ proper.subgroupOf cyclic := by rw [hequal]; trivial
      exact this
    exact hproper.not_ge hreverse
  have hle := proper_subgroup_le_squares_of_cyclic_two_group cyclic
    (htwogroup.to_subgroup cyclic) (proper.subgroupOf cyclic) hne
  have hrange := hle (show (⟨element, hproper.le hmember⟩ : cyclic) ∈
    proper.subgroupOf cyclic from hmember)
  obtain ⟨root, hroot⟩ := hrange
  exact ⟨root, root.property, congrArg Subtype.val hroot⟩

theorem zpowers_square_eq_center_of_rank_one_two_group (G : Type*) [Group G] [Finite G]
    (htwogroup : IsPGroup 2 G) (hrank : twoRank G ≤ 1) (element : G)
    (hnoncentral : element ∉ Subgroup.center G) (hsquare : element ^ 2 ∈ Subgroup.center G) :
    Subgroup.zpowers (element ^ 2) = Subgroup.center G := by
  apply le_antisymm (Subgroup.zpowers_le_of_mem hsquare)
  intro central hcentral
  obtain ⟨root, hrootmember, hroot⟩ := exists_square_root_in_cyclic_two_subgroup G htwogroup
    (Subgroup.zpowers element) (Subgroup.center G)
    (center_lt_zpowers_of_rank_one_two_group G htwogroup hrank element hnoncentral)
    central hcentral
  obtain ⟨power, hpower⟩ := Subgroup.mem_zpowers_iff.mp hrootmember
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨power, ?_⟩
  rw [← hroot, ← hpower]
  simpa only [zpow_ofNat] using
    (zpow_mul element (2 : ℤ) power).symm.trans (zpow_mul' element (2 : ℤ) power)

theorem exists_noncentral_with_central_quotient_involution (G : Type*)
    [Group G] [Finite G] (htwogroup : IsPGroup 2 G)
    (hnonabelian : ∃ left right : G, left * right ≠ right * left) :
    ∃ element : G, element ∉ Subgroup.center G ∧ element ^ 2 ∈ Subgroup.center G ∧
      (QuotientGroup.mk' (Subgroup.center G)) element ∈
        Subgroup.center (G ⧸ Subgroup.center G) := by
  have hcenterne : Subgroup.center G ≠ ⊤ := by
    intro hequal
    exact not_isMulCommutative_of_nonabelian G hnonabelian
      (Subgroup.center_eq_top_iff.mp hequal)
  have hquotientnontrivial : Nontrivial (G ⧸ Subgroup.center G) := by
    by_contra hnot
    have : Subsingleton (G ⧸ Subgroup.center G) :=
      not_nontrivial_iff_subsingleton.mp hnot
    apply hcenterne
    apply top_unique
    intro element _
    apply (QuotientGroup.eq_one_iff element).mp
    exact Subsingleton.elim _ _
  have hquotienttwo := htwogroup.of_surjective
    (QuotientGroup.mk' (Subgroup.center G)) (QuotientGroup.mk'_surjective _)
  obtain ⟨involution, horder, hcentral⟩ :=
    exists_central_involution_of_two_group (G ⧸ Subgroup.center G) hquotienttwo
  obtain ⟨element, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) involution
  refine ⟨element, ?_, ?_, hcentral⟩
  · intro hmember
    exact (orderOf_eq_prime_iff.mp horder).2 ((QuotientGroup.eq_one_iff element).mpr hmember)
  · apply (QuotientGroup.eq_one_iff (element ^ 2)).mp
    simpa only [QuotientGroup.mk_pow, QuotientGroup.mk'_apply] using
      (orderOf_eq_prime_iff.mp horder).1

theorem commuting_elements_same_order_eq_zpowers_of_rank_one_two_group
    (G : Type*) [Group G] [Finite G] (htwogroup : IsPGroup 2 G)
    (hrank : twoRank G ≤ 1) (left right : G) (hcommute : Commute left right)
    (horder : orderOf left = orderOf right) :
    Subgroup.zpowers left = Subgroup.zpowers right := by
  let generated := Subgroup.closure ({left, right} : Set G)
  have hab : IsMulCommutative generated := by
    apply CFSG.subgroup_isMulCommutative_closure
    intro first hfirst second hsecond
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hfirst hsecond
    rcases hfirst with rfl | rfl <;> rcases hsecond with rfl | rfl
    · rfl
    · exact hcommute
    · exact hcommute.symm
    · rfl
  have hcyclic : IsCyclic generated := by
    have := hab
    exact abelian_subgroup_of_rank_one_two_group_isCyclic G htwogroup hrank generated
  have hleft : Subgroup.zpowers left ≤ generated :=
    Subgroup.zpowers_le_of_mem (Subgroup.subset_closure (by simp))
  have hright : Subgroup.zpowers right ≤ generated :=
    Subgroup.zpowers_le_of_mem (Subgroup.subset_closure (by simp))
  obtain hle | hle := subgroups_comparable_of_cyclic_two_group generated
    (htwogroup.to_subgroup generated) ((Subgroup.zpowers left).subgroupOf generated)
    ((Subgroup.zpowers right).subgroupOf generated)
  · apply Subgroup.eq_of_le_of_card_ge
    · intro element hmember
      exact hle (show (⟨element, hleft hmember⟩ : generated) ∈
        (Subgroup.zpowers left).subgroupOf generated from hmember)
    · simp only [Nat.card_zpowers, horder, le_refl]
  · apply Eq.symm
    apply Subgroup.eq_of_le_of_card_ge
    · intro element hmember
      exact hle (show (⟨element, hright hmember⟩ : generated) ∈
        (Subgroup.zpowers right).subgroupOf generated from hmember)
    · simp only [Nat.card_zpowers, horder, le_refl]

theorem exists_noncommuting_pair_with_equal_central_squares (G : Type*)
    [Group G] [Finite G] (htwogroup : IsPGroup 2 G) (hrank : twoRank G ≤ 1)
    (hnonabelian : ∃ left right : G, left * right ≠ right * left) :
    ∃ left right : G, left * right ≠ right * left ∧ left ^ 2 = right ^ 2 ∧
      Subgroup.zpowers (left ^ 2) = Subgroup.center G ∧
      (QuotientGroup.mk' (Subgroup.center G)) left ∈
        Subgroup.center (G ⧸ Subgroup.center G) := by
  classical
  obtain ⟨left, hleftnoncentral, hleftsquare, hleftquotient⟩ :=
    exists_noncentral_with_central_quotient_involution G htwogroup hnonabelian
  have hnotall : ¬∀ other : G, other * left = left * other := by
    intro hall
    exact hleftnoncentral (Subgroup.mem_center_iff.mpr hall)
  obtain ⟨other, hother⟩ := not_forall.mp hnotall
  have hothernoncentral : other ∉ Subgroup.center G := by
    intro hcentral
    exact hother (Subgroup.mem_center_iff.mp hcentral left).symm
  obtain ⟨right, hrightmember, hrightsquare⟩ :=
    exists_square_root_in_cyclic_two_subgroup G htwogroup (Subgroup.zpowers other)
      (Subgroup.center G)
      (center_lt_zpowers_of_rank_one_two_group G htwogroup hrank other hothernoncentral)
      (left ^ 2) hleftsquare
  have hleftne : left ≠ 1 := by
    intro hequal
    exact hleftnoncentral (hequal ▸ Subgroup.one_mem _)
  have : Nontrivial G := nontrivial_of_ne left 1 hleftne
  have hrightne : right ≠ 1 := by
    intro hequal
    have hleftorder : orderOf left = 2 :=
      orderOf_eq_prime (by simpa [hequal] using hrightsquare.symm) hleftne
    have hcentral : left ∈ Subgroup.center G := by
      obtain ⟨involution, horder, hinvolutioncentral⟩ :=
        exists_central_involution_of_two_group G htwogroup
      have hequal := commuting_involutions_eq_of_twoRank_le_one G hrank left involution
        hleftorder horder (Subgroup.mem_center_iff.mp hinvolutioncentral left)
      rw [hequal]
      exact hinvolutioncentral
    exact hleftnoncentral hcentral
  have horders : orderOf left = orderOf right := by
    rw [square_order_doubled_of_two_group G htwogroup left hleftne,
      square_order_doubled_of_two_group G htwogroup right hrightne, hrightsquare]
  have hnoncommute : left * right ≠ right * left := by
    intro hcommute
    have hpowers := commuting_elements_same_order_eq_zpowers_of_rank_one_two_group
      G htwogroup hrank left right hcommute horders
    have hleftmember : left ∈ Subgroup.zpowers other := by
      apply (Subgroup.zpowers_le_of_mem hrightmember)
      rw [← hpowers]
      exact Subgroup.mem_zpowers left
    have hcommutative := Subgroup.le_centralizer (Subgroup.zpowers other)
    exact hother (Subgroup.mem_centralizer_iff.mp
      (hcommutative hleftmember) other (Subgroup.mem_zpowers other))
  exact ⟨left, right, hnoncommute, hrightsquare.symm,
    zpowers_square_eq_center_of_rank_one_two_group G htwogroup hrank left
      hleftnoncentral hleftsquare, hleftquotient⟩

end CFSG.TwoRankLowerBound.Helpers
