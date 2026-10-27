module

public import CFSG.CharacterTheory.TwoRankLowerBound.Helpers

public section

open CFSG.Open

namespace CFSG.TwoRankLowerBound.Helpers

def involutionPairSubgroup {G : Type*} [Group G] (left right : G)
    (hleft : left ^ 2 = 1) (hright : right ^ 2 = 1) (hcommute : Commute left right) :
    Subgroup G where
  carrier := {1, left, right, left * right}
  one_mem' := by simp
  mul_mem' := by
    intro first second hfirst hsecond
    have hleftmul : left * left = 1 := by simpa [pow_two] using hleft
    have hrightmul : right * right = 1 := by simpa [pow_two] using hright
    have hleftrightleft : left * (right * left) = right := by
      rw [← hcommute.eq, ← mul_assoc, hleftmul, one_mul]
    have hrightleftright : right * (left * right) = left := by
      rw [hcommute.eq, ← mul_assoc, hrightmul, one_mul]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hfirst hsecond ⊢
    rcases hfirst with rfl | rfl | rfl | rfl <;>
      rcases hsecond with rfl | rfl | rfl | rfl <;>
      simp_all [mul_assoc, ← hcommute.eq]
  inv_mem' := by
    intro element helement
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at helement ⊢
    have hleftinv : left⁻¹ = left := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hleft)
    have hrightinv : right⁻¹ = right := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hright)
    rcases helement with rfl | rfl | rfl | rfl <;>
      simp_all [mul_inv_rev, ← hcommute.eq]

theorem involutionPairSubgroup_elementary {G : Type*} [Group G] (left right : G)
    (hleft : left ^ 2 = 1) (hright : right ^ 2 = 1) (hcommute : Commute left right) :
    IsElemAbelian 2 (involutionPairSubgroup left right hleft hright hcommute) := by
  constructor
  · apply IsMulCommutative.of_setLike_mul_comm
    intro first hfirst second hsecond
    change first ∈ ({1, left, right, left * right} : Set G) at hfirst
    change second ∈ ({1, left, right, left * right} : Set G) at hsecond
    have hleftmul : left * left = 1 := by simpa [pow_two] using hleft
    have hrightmul : right * right = 1 := by simpa [pow_two] using hright
    have hleftrightleft : left * (right * left) = right := by
      rw [← hcommute.eq, ← mul_assoc, hleftmul, one_mul]
    have hrightleftright : right * (left * right) = left := by
      rw [hcommute.eq, ← mul_assoc, hrightmul, one_mul]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hfirst hsecond
    rcases hfirst with rfl | rfl | rfl | rfl <;>
      rcases hsecond with rfl | rfl | rfl | rfl <;>
      simp_all [mul_assoc, ← hcommute.eq]
  · intro element helement
    change element ∈ ({1, left, right, left * right} : Set G) at helement
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at helement
    rcases helement with rfl | rfl | rfl | rfl
    · simp
    · exact hleft
    · exact hright
    · rw [hcommute.mul_pow, hleft, hright, one_mul]

theorem involutionPairSubgroup_card {G : Type*} [Group G] (left right : G)
    (hleft : orderOf left = 2) (hright : orderOf right = 2) (hne : left ≠ right)
    (hcommute : Commute left right) :
    Nat.card (involutionPairSubgroup left right (hleft ▸ pow_orderOf_eq_one left)
      (hright ▸ pow_orderOf_eq_one right) hcommute) = 4 := by
  have hleftne : left ≠ 1 := by
    intro heq
    simp [heq] at hleft
  have hrightne : right ≠ 1 := by
    intro heq
    simp [heq] at hright
  have hproductne := mul_notMem_of_orderOf_eq_two hleft hright hne
  have hproductleft : left * right ≠ left := by
    intro heq
    exact hproductne (by simp [heq])
  have hproductright : left * right ≠ right := by
    intro heq
    exact hproductne (by simp [heq])
  have hproductone : left * right ≠ 1 := by
    intro heq
    exact hproductne (by simp [heq])
  change Nat.card ({1, left, right, left * right} : Set G) = 4
  rw [Nat.card_coe_set_eq]
  rw [Set.ncard_insert_of_notMem (by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hleftne.symm, hrightne.symm, hproductone.symm⟩),
    Set.ncard_insert_of_notMem (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne, hproductleft.symm⟩),
    Set.ncard_insert_of_notMem (by
      simp only [Set.mem_singleton_iff]
      exact hproductright.symm)]
  simp

theorem two_le_twoRank_of_commuting_involutions (G : Type*) [Group G] [Finite G]
    (left right : G) (hleft : orderOf left = 2) (hright : orderOf right = 2)
    (hne : left ≠ right) (hcommute : Commute left right) : 2 ≤ twoRank G := by
  apply le_twoRank_of_elementary G
    (involutionPairSubgroup left right (hleft ▸ pow_orderOf_eq_one left)
      (hright ▸ pow_orderOf_eq_one right) hcommute)
    (involutionPairSubgroup_elementary left right _ _ hcommute) 2
  simpa using involutionPairSubgroup_card left right hleft hright hne hcommute

theorem commuting_involutions_eq_of_twoRank_le_one (G : Type*) [Group G] [Finite G]
    (hrank : twoRank G ≤ 1) (left right : G) (hleft : orderOf left = 2)
    (hright : orderOf right = 2) (hcommute : Commute left right) : left = right := by
  by_contra hne
  have := two_le_twoRank_of_commuting_involutions G left right hleft hright hne hcommute
  omega

end CFSG.TwoRankLowerBound.Helpers
