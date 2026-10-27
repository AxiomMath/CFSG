module

public import CFSG.Assembly.OrderReductions.InvolutionFusion

public section

namespace CFSG.OrderReductions.OutsideInvolutions

open CFSG.OrderReductions.InvolutionGraph

abbrev Outside {group : Type*} [Group group] (subgroup : Subgroup group) :=
  {involution : Involution group // involution.val ∉ subgroup}

theorem conjugate_mem_of_mem {group : Type*} [Group group]
    (subgroup : Subgroup group) (conjugator : group) (involution : Involution group)
    (conjugator_mem : conjugator ∈ subgroup) (involution_mem : involution.val ∈ subgroup) :
    (conjugator • involution).val ∈ subgroup := by
  rw [involution_smul_val]
  exact subgroup.mul_mem (subgroup.mul_mem conjugator_mem involution_mem)
    (subgroup.inv_mem conjugator_mem)

@[expose] def outsideConjugation {group : Type*} [Group group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (first : Involution group) (first_mem : first.val ∈ subgroup)
    (outside : Outside subgroup) : Outside subgroup :=
  ⟨outside.val.val • first, by
    intro conjugated_mem
    exact outside.property (stronglyEmbedded_involution_conjugator_mem subgroup strong
      first first_mem outside.val.val conjugated_mem)⟩

theorem outsideConjugation_bijective {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (first : Involution group) (first_mem : first.val ∈ subgroup) :
    Function.Bijective (outsideConjugation subgroup strong first first_mem) := by
  have surjective : Function.Surjective (outsideConjugation subgroup strong first first_mem) := by
    intro outside
    have not_reachable : ¬ (commutingGraph group).Reachable first outside.val := by
      intro reachable
      exact outside.property (stronglyEmbedded_reachable_mem subgroup strong first outside.val
        first_mem reachable)
    have distinct : first ≠ outside.val := by
      intro equal_vertices
      exact outside.property (equal_vertices ▸ first_mem)
    obtain ⟨conjugator, conjugates⟩ :=
      CFSG.OrderReductions.InvolutionFusion.involution_conjugator_of_odd_product_order first outside.val
        distinct (CFSG.OrderReductions.InvolutionFusion.odd_product_order_of_not_reachable
          first outside.val not_reachable)
    have not_mem : conjugator.val ∉ subgroup := by
      intro mem_subgroup
      have conjugated_mem := conjugate_mem_of_mem subgroup conjugator.val first
        mem_subgroup first_mem
      rw [conjugates] at conjugated_mem
      exact outside.property conjugated_mem
    exact ⟨⟨conjugator, not_mem⟩, Subtype.ext conjugates⟩
  exact ⟨Finite.injective_iff_surjective.mpr surjective, surjective⟩

theorem unique_outside_conjugator {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (first second : Involution group) (first_mem : first.val ∈ subgroup)
    (second_not_mem : second.val ∉ subgroup) :
    ∃! conjugator : Involution group, conjugator.val • first = second := by
  obtain ⟨conjugator, conjugates⟩ :=
    (outsideConjugation_bijective subgroup strong first first_mem).surjective
      ⟨second, second_not_mem⟩
  have moves : conjugator.val.val • first = second := congrArg Subtype.val conjugates
  refine ⟨conjugator.val, moves, ?_⟩
  intro other other_moves
  have other_not_mem : other.val ∉ subgroup := by
    intro other_mem
    have conjugated_mem := conjugate_mem_of_mem subgroup other.val first other_mem first_mem
    rw [other_moves] at conjugated_mem
    exact second_not_mem conjugated_mem
  have equal_images : outsideConjugation subgroup strong first first_mem ⟨other, other_not_mem⟩ =
      outsideConjugation subgroup strong first first_mem conjugator := by
    apply Subtype.ext
    exact other_moves.trans moves.symm
  exact congrArg Subtype.val
    ((outsideConjugation_bijective subgroup strong first first_mem).injective equal_images)

abbrev InvertedBy {group : Type*} [Group group] (subgroup : Subgroup group)
    (involution : Involution group) :=
  {element : subgroup // (MulAut.conj involution.val) element.val = element.val⁻¹}

theorem inverted_conjugation_injective {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (first outside : Involution group) (first_mem : first.val ∈ subgroup)
    (outside_not_mem : outside.val ∉ subgroup) :
    Function.Injective (fun element : InvertedBy subgroup outside => element.val.val • first) := by
  intro first_element second_element equal_images
  change first_element.val.val • first = second_element.val.val • first at equal_images
  have reflected_involution (element : InvertedBy subgroup outside) :
      orderOf (outside.val * element.val.val) = 2 := by
    have square_one : (outside.val * element.val.val) ^ 2 = 1 := by
      have inversion := element.property
      rw [MulAut.conj_apply, inv_eq_self_of_orderOf_eq_two outside.property] at inversion
      rw [pow_two, ← mul_assoc]
      rw [inversion, inv_mul_cancel]
    have not_mem : outside.val * element.val.val ∉ subgroup := by
      intro product_mem
      have outside_mem := subgroup.mul_mem product_mem (subgroup.inv_mem element.val.property)
      rw [mul_assoc, mul_inv_cancel, mul_one] at outside_mem
      exact outside_not_mem outside_mem
    rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp
      (orderOf_dvd_of_pow_eq_one square_one) with order_one | order_two
    · exact False.elim (not_mem ((orderOf_eq_one_iff.mp order_one) ▸ subgroup.one_mem))
    · exact order_two
  let first_reflection : Involution group :=
    ⟨outside.val * first_element.val.val, reflected_involution first_element⟩
  let second_reflection : Involution group :=
    ⟨outside.val * second_element.val.val, reflected_involution second_element⟩
  have first_not_mem : first_reflection.val ∉ subgroup := by
    intro product_mem
    have outside_mem := subgroup.mul_mem product_mem (subgroup.inv_mem first_element.val.property)
    change (outside.val * first_element.val.val) * first_element.val.val⁻¹ ∈ subgroup at outside_mem
    rw [mul_assoc, mul_inv_cancel, mul_one] at outside_mem
    exact outside_not_mem outside_mem
  have second_not_mem : second_reflection.val ∉ subgroup := by
    intro product_mem
    have outside_mem := subgroup.mul_mem product_mem (subgroup.inv_mem second_element.val.property)
    change (outside.val * second_element.val.val) * second_element.val.val⁻¹ ∈ subgroup at outside_mem
    rw [mul_assoc, mul_inv_cancel, mul_one] at outside_mem
    exact outside_not_mem outside_mem
  have reflected_images : outsideConjugation subgroup strong first first_mem
      ⟨first_reflection, first_not_mem⟩ =
      outsideConjugation subgroup strong first first_mem ⟨second_reflection, second_not_mem⟩ := by
    apply Subtype.ext
    change (outside.val * first_element.val.val) • first =
      (outside.val * second_element.val.val) • first
    rw [mul_smul, mul_smul, equal_images]
  have equal_reflections := congrArg (fun element : Outside subgroup => element.val.val)
    ((outsideConjugation_bijective subgroup strong first first_mem).injective reflected_images)
  apply Subtype.ext
  apply Subtype.ext
  exact mul_left_cancel equal_reflections

end CFSG.OrderReductions.OutsideInvolutions
