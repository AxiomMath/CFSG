module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneCenterTwo
public import CFSG.Dihedral.DisconnectedInvolutionGraph.IndexTwoCosets

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem rank_one_two_cyclic_index_two_outside_squares
    (hpgroup : IsPGroup 2 G) (hrank : NoCommutingDistinctInvolutions G)
    (hnonabelian : ∃ first second : G, first * second ≠ second * first)
    (subgroup : Subgroup G) (hindex : subgroup.index = 2) (hcyclic : IsCyclic subgroup)
    (element : G) (helementOutside : element ∉ subgroup) (helementOrder : orderOf element = 4)
    (other : G) (hotherOutside : other ∉ subgroup) : other ^ 2 = element ^ 2 := by
  classical
  let _ := Subgroup.normal_of_index_eq_two hindex
  have helementSquareMem : element ^ 2 ∈ subgroup := by
    simpa only [hindex] using subgroup.pow_index_mem element
  have helementSquareCentral := cyclic_index_two_outside_square_central subgroup
    hindex hcyclic element helementOutside
  have hotherSquareCentral := cyclic_index_two_outside_square_central subgroup
    hindex hcyclic other hotherOutside
  have helementSquareOrder : orderOf (element ^ 2) = 2 := by
    rw [orderOf_pow, helementOrder]
    norm_num
  have helementSquareNe : element ^ 2 ≠ 1 := by
    intro hone
    rw [hone, orderOf_one] at helementSquareOrder
    omega
  have hotherSquareNe : other ^ 2 ≠ 1 := by
    intro hone
    have hotherNe : other ≠ 1 := fun heq => hotherOutside (heq ▸ subgroup.one_mem)
    let otherInvolution : Involution G := ⟨other, orderOf_eq_prime hone hotherNe⟩
    let squareInvolution : Involution G := ⟨element ^ 2, helementSquareOrder⟩
    have hequal := hrank otherInvolution squareInvolution
      (Subgroup.mem_center_iff.mp helementSquareCentral other)
    have hambient : other = element ^ 2 := congrArg Subtype.val hequal
    exact hotherOutside (hambient ▸ helementSquareMem)
  have hcenterCard := rank_one_two_nonabelian_center_card_two hpgroup hrank hnonabelian
  obtain ⟨unique, _, hunique⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center G)).mp hcenterCard
  let firstSquare : Subgroup.center G := ⟨other ^ 2, hotherSquareCentral⟩
  let secondSquare : Subgroup.center G := ⟨element ^ 2, helementSquareCentral⟩
  have hfirstNe : firstSquare ≠ 1 := fun heq => hotherSquareNe (congrArg Subtype.val heq)
  have hsecondNe : secondSquare ≠ 1 := fun heq => helementSquareNe (congrArg Subtype.val heq)
  exact congrArg Subtype.val ((hunique firstSquare hfirstNe).trans
    (hunique secondSquare hsecondNe).symm)

theorem rank_one_two_cyclic_index_two_inversion
    (hpgroup : IsPGroup 2 G) (hrank : NoCommutingDistinctInvolutions G)
    (hnonabelian : ∃ first second : G, first * second ≠ second * first)
    (subgroup : Subgroup G) (hindex : subgroup.index = 2) (hcyclic : IsCyclic subgroup)
    (element : G) (helementOutside : element ∉ subgroup) (helementOrder : orderOf element = 4)
    (other : G) (hother : other ∈ subgroup) : element * other * element⁻¹ = other⁻¹ := by
  have hproductOutside : other * element ∉ subgroup := by
    intro hmem
    have helementMem := subgroup.mul_mem (subgroup.inv_mem hother) hmem
    exact helementOutside (by simpa only [inv_mul_cancel_left] using helementMem)
  have hproductSquare := rank_one_two_cyclic_index_two_outside_squares hpgroup hrank
    hnonabelian subgroup hindex hcyclic element helementOutside helementOrder
    (other * element) hproductOutside
  calc
    element * other * element⁻¹ =
        other⁻¹ * (other * element) ^ 2 * element⁻¹ * element⁻¹ := by
      simp only [pow_two, mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one]
    _ = other⁻¹ * element ^ 2 * element⁻¹ * element⁻¹ := by rw [hproductSquare]
    _ = other⁻¹ := by group

end CFSG.DisconnectedInvolutionGraph.Helpers
