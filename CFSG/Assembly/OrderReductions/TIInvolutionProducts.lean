module

public import CFSG.Assembly.OrderReductions.InvolutionFusion
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.OrderReductions.TIInvolutionProducts

open CFSG.OrderReductions.InvolutionGraph

@[expose] def conjugateSet {group : Type*} [Group group] (support : Set group) (conjugator : group) : Set group :=
  (fun element => conjugator * element * conjugator⁻¹) '' support

@[expose] def TI {group : Type*} [Group group] (support : Set group) (normalizer : Subgroup group) : Prop :=
  support.Nonempty ∧ (1 : group) ∉ support ∧ Subgroup.normalizer support = normalizer ∧
    ∀ conjugator : group, conjugator ∉ normalizer → Disjoint support (conjugateSet support conjugator)

theorem mem_normalizer_of_overlap {group : Type*} [Group group]
    (support : Set group) (normalizer : Subgroup group) (ti : TI support normalizer)
    (conjugator element : group) (element_mem : element ∈ support)
    (conjugate_mem : conjugator * element * conjugator⁻¹ ∈ support) : conjugator ∈ normalizer := by
  classical
  by_contra outside
  exact Set.disjoint_left.mp (ti.2.2.2 conjugator outside) conjugate_mem
    ⟨element, element_mem, rfl⟩

theorem product_in_support_factors_mem_normalizer {group : Type*} [Group group]
    (support : Set group) (normalizer : Subgroup group) (ti : TI support normalizer)
    (inverse_stable : ∀ element ∈ support, element⁻¹ ∈ support)
    (first second : Involution group) (product_mem : first.val * second.val ∈ support) :
    first.val ∈ normalizer ∧ second.val ∈ normalizer := by
  have inverse_mem := inverse_stable _ product_mem
  have first_conjugate : first.val * (first.val * second.val) * first.val⁻¹ =
      (first.val * second.val)⁻¹ :=
    CFSG.OrderReductions.InvolutionFusion.product_conjugate_inv first second
  have second_conjugate : second.val * (first.val * second.val) * second.val⁻¹ =
      (first.val * second.val)⁻¹ := by
    have second_inverse := inv_eq_self_of_orderOf_eq_two second.property
    have first_inverse := inv_eq_self_of_orderOf_eq_two first.property
    rw [mul_inv_rev, first_inverse, second_inverse, mul_assoc, mul_assoc,
      CFSG.OrderReductions.InvolutionFusion.involution_mul_self second, mul_one]
  exact ⟨mem_normalizer_of_overlap support normalizer ti first.val _ product_mem
    (first_conjugate.symm ▸ inverse_mem),
    mem_normalizer_of_overlap support normalizer ti second.val _ product_mem
      (second_conjugate.symm ▸ inverse_mem)⟩

end CFSG.OrderReductions.TIInvolutionProducts
