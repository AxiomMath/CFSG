module

public import CFSG.CharacterTheory.TwoRankLowerBound.OrderFourOutside

public section

open CFSG.Open

namespace CFSG.TwoRankLowerBound.Helpers

theorem square_mem_center_of_outside_cyclic_index_two (G : Type*) [Group G]
    (cyclic : Subgroup G) [IsCyclic cyclic] (hindex : cyclic.index = 2)
    (element : G) (houtside : element ∉ cyclic) : element ^ 2 ∈ Subgroup.center G := by
  have hsquare : element ^ 2 ∈ cyclic := cyclic.sq_mem_of_index_two hindex element
  have hcommute : ∀ member : G, member ∈ cyclic → Commute member (element ^ 2) := by
    intro member hmember
    have hcentralizer := Subgroup.le_centralizer cyclic
    exact Subgroup.mem_centralizer_iff.mp (hcentralizer hsquare) member hmember
  apply Subgroup.mem_center_iff.mpr
  intro other
  by_cases hother : other ∈ cyclic
  · exact hcommute other hother
  · have hinverseoutside : element⁻¹ ∉ cyclic := by
      intro hinverse
      exact houtside ((cyclic.inv_mem_iff).mp hinverse)
    have hdifference : other * element⁻¹ ∈ cyclic :=
      (Subgroup.mul_mem_iff_of_index_two hindex).mpr ⟨fun h => False.elim (hother h),
        fun h => False.elim (hinverseoutside h)⟩
    have hproductcommute := (hcommute (other * element⁻¹) hdifference).mul_left
      ((Commute.refl element).pow_right 2)
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hproductcommute.eq

theorem outside_cyclic_index_two_squares_equal (G : Type*) [Group G] [Finite G]
    (htwogroup : IsPGroup 2 G) (hrank : twoRank G ≤ 1)
    (cyclic : Subgroup G) [IsCyclic cyclic] (hindex : cyclic.index = 2)
    (hcenterle : Subgroup.center G ≤ cyclic) (hcentertwo : Nat.card (Subgroup.center G) = 2)
    (left right : G) (hleft : left ∉ cyclic) (hright : right ∉ cyclic) :
    left ^ 2 = right ^ 2 := by
  have hcentral : ∀ element : G, element ∉ cyclic → element ^ 2 ∈ Subgroup.center G :=
    fun element houtside => square_mem_center_of_outside_cyclic_index_two G cyclic hindex
      element houtside
  have hsquarene : ∀ element : G, element ∉ cyclic → element ^ 2 ≠ 1 := by
    intro element houtside hsquare
    have hne : element ≠ 1 := by
      intro hequal
      exact houtside (hequal ▸ cyclic.one_mem)
    exact houtside (hcenterle (involution_mem_center_of_rank_one_two_group G htwogroup hrank
      element (orderOf_eq_prime hsquare hne)))
  have hsquareorder : ∀ element : G, element ∉ cyclic → orderOf (element ^ 2) = 2 := by
    intro element houtside
    have hdivides := (Subgroup.center G).orderOf_dvd_natCard (hcentral element houtside)
    rw [hcentertwo] at hdivides
    obtain hone | htwo := (Nat.dvd_prime Nat.prime_two).mp hdivides
    · exact False.elim (hsquarene element houtside (orderOf_eq_one_iff.mp hone))
    · exact htwo
  exact commuting_involutions_eq_of_twoRank_le_one G hrank (left ^ 2) (right ^ 2)
    (hsquareorder left hleft) (hsquareorder right hright)
    (Subgroup.mem_center_iff.mp (hcentral right hright) (left ^ 2))

theorem outside_cyclic_index_two_conjugates_by_inversion (G : Type*)
    [Group G] [Finite G] (htwogroup : IsPGroup 2 G) (hrank : twoRank G ≤ 1)
    (cyclic : Subgroup G) [IsCyclic cyclic] (hindex : cyclic.index = 2)
    (hcenterle : Subgroup.center G ≤ cyclic) (hcentertwo : Nat.card (Subgroup.center G) = 2)
    (outside : G) (houtside : outside ∉ cyclic) (member : G) (hmember : member ∈ cyclic) :
    outside * member * outside⁻¹ = member⁻¹ := by
  have hproductoutside : member * outside ∉ cyclic := by
    intro hproduct
    exact houtside (((Subgroup.mul_mem_iff_of_index_two hindex).mp hproduct).mp hmember)
  have hsquare := outside_cyclic_index_two_squares_equal G htwogroup hrank cyclic hindex
    hcenterle hcentertwo (member * outside) outside hproductoutside houtside
  have hconjugate := congrArg (fun element : G => member⁻¹ * element * outside⁻¹ * outside⁻¹)
    hsquare
  simpa only [pow_two, mul_assoc, inv_mul_cancel, mul_inv_cancel, mul_one, one_mul,
    inv_mul_cancel_left] using
    hconjugate

end CFSG.TwoRankLowerBound.Helpers
