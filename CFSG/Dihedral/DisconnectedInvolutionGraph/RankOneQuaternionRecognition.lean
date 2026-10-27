module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneOrderFourOutside
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRelations
public import CFSG.Dihedral.DisconnectedInvolutionGraph.QuaternionCoordinateEquiv

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem rank_one_two_nonabelian_quaternion
    (hpgroup : IsPGroup 2 G) (hrank : NoCommutingDistinctInvolutions G)
    (hnonabelian : ∃ first second : G, first * second ≠ second * first) :
    ∃ exponent : ℕ, 1 ≤ exponent ∧ Nonempty (QuaternionGroup (2 ^ exponent) ≃* G) := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨normalSubgroup, _, hnormalCyclic, hnormalCard, hindex, hcyclic⟩ :=
    rank_one_two_exists_cyclic_index_two hpgroup hrank hnonabelian
  let subgroup := Subgroup.centralizer (normalSubgroup : Set G)
  let _ := hnormalCyclic
  let _ := hcyclic
  have hnormalLe : normalSubgroup ≤ subgroup := by
    intro element helement
    apply Subgroup.mem_centralizer_iff.mpr
    intro other hother
    exact congrArg (fun inside : normalSubgroup => inside.val)
      (mul_comm' (⟨other, hother⟩ : normalSubgroup) ⟨element, helement⟩)
  have hsubgroupCardGe : 4 ≤ Nat.card subgroup := by
    rw [← hnormalCard]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hnormalLe)
  obtain ⟨exponent, hcard⟩ := IsPGroup.iff_card.mp (hpgroup.to_subgroup subgroup)
  have hexponentGe : 2 ≤ exponent := by
    by_contra hsmall
    have hcases : exponent = 0 ∨ exponent = 1 := by omega
    rcases hcases with rfl | rfl
    · rw [hcard, pow_zero] at hsubgroupCardGe
      omega
    · rw [hcard, pow_one] at hsubgroupCardGe
      omega
  let size := 2 ^ (exponent - 1)
  have hcardSize : Nat.card subgroup = 2 * size := by
    rw [hcard]
    change 2 ^ exponent = 2 * 2 ^ (exponent - 1)
    conv_lhs => rw [show exponent = exponent - 1 + 1 by omega]
    rw [pow_succ']
  let coordinatesEquiv : Multiplicative (ZMod (2 * size)) ≃* subgroup :=
    (MulEquiv.refl _).trans (by
      rw [← hcardSize]
      exact zmodCyclicMulEquiv hcyclic)
  let coordinates : Multiplicative (ZMod (2 * size)) →* G :=
    subgroup.subtype.comp coordinatesEquiv.toMonoidHom
  have hinjective : Function.Injective coordinates :=
    Subtype.val_injective.comp coordinatesEquiv.injective
  have hrange : coordinates.range = subgroup := by
    ext element
    constructor
    · rintro ⟨coordinate, rfl⟩
      exact (coordinatesEquiv coordinate).property
    · intro hmem
      obtain ⟨coordinate, hcoordinate⟩ := coordinatesEquiv.surjective ⟨element, hmem⟩
      exact ⟨coordinate, congrArg Subtype.val hcoordinate⟩
  obtain ⟨outside, houtside, houtsideOrder⟩ :=
    rank_one_two_exists_order_four_outside_cyclic hpgroup hrank hnonabelian subgroup hcyclic
  have hsizePositive : 0 < size := pow_pos (by decide) _
  have hsizeNe : size ≠ 0 := hsizePositive.ne'
  have hsizeDvd : size ∣ 2 * size := ⟨2, by omega⟩
  let involutionCoordinate := Multiplicative.ofAdd (size : ZMod (2 * size))
  have hcoordinateOrder : orderOf involutionCoordinate = 2 := by
    rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_coe size
      (by omega : 2 * size ≠ 0), Nat.gcd_eq_right hsizeDvd,
      Nat.mul_div_cancel 2 hsizePositive]
  have himageOrder : orderOf (coordinates involutionCoordinate) = 2 :=
    (orderOf_injective coordinates hinjective involutionCoordinate).trans hcoordinateOrder
  have houtsideSquareOrder : orderOf (outside ^ 2) = 2 := by
    rw [orderOf_pow, houtsideOrder]
    norm_num
  have houtsideSquareCentral := cyclic_index_two_outside_square_central subgroup hindex
    hcyclic outside houtside
  have hsquare : outside ^ 2 = coordinates involutionCoordinate := by
    let first : Involution G := ⟨outside ^ 2, houtsideSquareOrder⟩
    let second : Involution G := ⟨coordinates involutionCoordinate, himageOrder⟩
    have hequal := hrank first second
      (Subgroup.mem_center_iff.mp houtsideSquareCentral (coordinates involutionCoordinate)).symm
    exact congrArg Subtype.val hequal
  have hinversion : ∀ coordinate, outside * coordinates coordinate * outside⁻¹ =
      (coordinates coordinate)⁻¹ := by
    intro coordinate
    exact rank_one_two_cyclic_index_two_inversion hpgroup hrank hnonabelian subgroup hindex
      hcyclic outside houtside houtsideOrder (coordinates coordinate)
      (by rw [← hrange]; exact ⟨coordinate, rfl⟩)
  refine ⟨exponent - 1, by omega, ?_⟩
  exact ⟨quaternionCoordinateEquiv size coordinates outside hsquare hinversion hinjective
    (by rw [hrange]; exact hindex) (by rw [hrange]; exact houtside)⟩

theorem rank_one_two_cyclic_or_quaternion
    (hpgroup : IsPGroup 2 G) (hrank : NoCommutingDistinctInvolutions G) :
    IsCyclic G ∨ ∃ exponent : ℕ, 1 ≤ exponent ∧
      Nonempty (QuaternionGroup (2 ^ exponent) ≃* G) := by
  classical
  by_cases hnonabelian : ∃ first second : G, first * second ≠ second * first
  · exact Or.inr (rank_one_two_nonabelian_quaternion hpgroup hrank hnonabelian)
  · left
    have hcommute : ∀ first second : G, first * second = second * first := by
      simpa only [not_exists, not_not] using hnonabelian
    let _ : CommGroup G := { (inferInstance : Group G) with mul_comm := hcommute }
    exact rank_one_abelian_two_group_cyclic G hpgroup hrank

end CFSG.DisconnectedInvolutionGraph.Helpers
