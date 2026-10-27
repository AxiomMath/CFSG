module

public import Mathlib
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.TensorProduct.Finite
public import CFSG.Assembly.OrderReductions.InvolutionGraph
public import CFSG.Assembly.OrderReductions.InvolutionFusion
public import CFSG.Assembly.OrderReductions.StrongEmbedding
public import CFSG.Assembly.OrderReductions.StrongEmbeddingInheritance
public import CFSG.Assembly.OrderReductions.InvariantSylow
public import CFSG.Assembly.OrderReductions.InvariantQuotient
public import CFSG.Assembly.OrderReductions.FourGroupGeneration

public section

namespace CFSG.OrderReductions.RankTwoContainment

open CFSG.OrderReductions.InvolutionGraph

theorem commuting_involution_product {group : Type*} [Group group]
    (first second : Involution group) (distinct : first ≠ second)
    (commutes : Commute first.val second.val) : orderOf (first.val * second.val) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  apply orderOf_eq_prime
  · rw [commutes.mul_pow]
    have first_square : first.val ^ 2 = 1 := by
      simpa only [first.property] using pow_orderOf_eq_one first.val
    have second_square : second.val ^ 2 = 1 := by
      simpa only [second.property] using pow_orderOf_eq_one second.val
    rw [first_square, second_square, one_mul]
  · intro product_one
    have equal_values : first.val = second.val := by
      calc
        first.val = second.val⁻¹ := mul_eq_one_iff_eq_inv.mp product_one
        _ = second.val := inv_eq_self_of_orderOf_eq_two second.property
    exact distinct (Subtype.ext equal_values)

theorem conjugation_involutive_of_involution {group : Type*} [Group group]
    (involution : Involution group) (subgroup : Subgroup group)
    (invariant : subgroup.map (MulAut.conj involution.val).toMonoidHom = subgroup) :
    Function.Involutive (CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism
      (MulAut.conj involution.val) subgroup invariant) := by
  apply CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism_involutive
  intro element
  have square_one := CFSG.OrderReductions.InvolutionFusion.involution_mul_self involution
  rw [MulAut.conj_apply, MulAut.conj_apply,
    inv_eq_self_of_orderOf_eq_two involution.property]
  calc
    involution.val * (involution.val * element * involution.val) * involution.val =
        (involution.val * involution.val) * element * (involution.val * involution.val) := by group
    _ = element := by rw [square_one, one_mul, mul_one]

theorem odd_normalized_subgroup_le_of_four_involutions {group : Type*}
    [Group group] [Finite group] (subgroup ambient : Subgroup group)
    (odd_subgroup : Odd (Nat.card subgroup)) (first second : Involution group)
    (_distinct : first ≠ second) (commutes : Commute first.val second.val)
    (first_normalizes : subgroup.map (MulAut.conj first.val).toMonoidHom = subgroup)
    (second_normalizes : subgroup.map (MulAut.conj second.val).toMonoidHom = subgroup)
    (first_centralizer : Subgroup.centralizer ({first.val} : Set group) ≤ ambient)
    (second_centralizer : Subgroup.centralizer ({second.val} : Set group) ≤ ambient)
    (product_centralizer : Subgroup.centralizer ({first.val * second.val} : Set group) ≤ ambient) :
    subgroup ≤ ambient := by
  apply Subgroup.subgroupOf_eq_top.mp
  let first_action := CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism
    (MulAut.conj first.val) subgroup first_normalizes
  let second_action := CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism
    (MulAut.conj second.val) subgroup second_normalizes
  have actions_commute : ∀ element : subgroup,
      first_action (second_action element) = second_action (first_action element) := by
    apply CFSG.OrderReductions.InvariantQuotient.restrictedAutomorphism_commutes
    intro element
    have automorphisms_commute := commutes.map MulAut.conj
    exact congrArg (fun automorphism : MulAut group => automorphism element) automorphisms_commute.eq
  apply CFSG.OrderReductions.FourGroupGeneration.odd_four_involution_generation odd_subgroup
    first_action second_action
    (conjugation_involutive_of_involution first subgroup first_normalizes)
    (conjugation_involutive_of_involution second subgroup second_normalizes) actions_commute
  · intro element fixed
    apply first_centralizer
    rw [Subgroup.mem_centralizer_iff]
    intro other other_mem
    have other_eq : other = first.val := by simpa only [Set.mem_singleton_iff] using other_mem
    rw [other_eq]
    have conjugation_fixed : first.val * element.val * first.val⁻¹ = element.val :=
      congrArg Subtype.val fixed
    exact mul_inv_eq_iff_eq_mul.mp conjugation_fixed
  · intro element fixed
    apply second_centralizer
    rw [Subgroup.mem_centralizer_iff]
    intro other other_mem
    have other_eq : other = second.val := by simpa only [Set.mem_singleton_iff] using other_mem
    rw [other_eq]
    have conjugation_fixed : second.val * element.val * second.val⁻¹ = element.val :=
      congrArg Subtype.val fixed
    exact mul_inv_eq_iff_eq_mul.mp conjugation_fixed
  · intro element fixed
    apply product_centralizer
    rw [Subgroup.mem_centralizer_iff]
    intro other other_mem
    have other_eq : other = first.val * second.val := by
      simpa only [Set.mem_singleton_iff] using other_mem
    rw [other_eq]
    have conjugation_fixed : (MulAut.conj first.val) ((MulAut.conj second.val) element.val) =
        element.val := congrArg Subtype.val fixed
    change (MulAut.conj first.val * MulAut.conj second.val : MulAut group) element.val =
      element.val at conjugation_fixed
    rw [← MulAut.conj.map_mul] at conjugation_fixed
    exact mul_inv_eq_iff_eq_mul.mp conjugation_fixed

theorem odd_normal_le_of_four_involutions_mem {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (normal : Subgroup group) [normal.Normal] (odd_normal : Odd (Nat.card normal))
    (first second : Involution group) (distinct : first ≠ second)
    (commutes : Commute first.val second.val)
    (first_mem : first.val ∈ subgroup) (second_mem : second.val ∈ subgroup) :
    normal ≤ subgroup := by
  let product : Involution group :=
    ⟨first.val * second.val, commuting_involution_product first second distinct commutes⟩
  exact odd_normalized_subgroup_le_of_four_involutions normal subgroup odd_normal
    first second distinct commutes
    (Subgroup.Normal.map_conj_eq normal first.val)
    (Subgroup.Normal.map_conj_eq normal second.val)
    (stronglyEmbedded_centralizer_le subgroup strong first first_mem)
    (stronglyEmbedded_centralizer_le subgroup strong second second_mem)
    (stronglyEmbedded_centralizer_le subgroup strong product (subgroup.mul_mem first_mem second_mem))

theorem odd_normal_le_of_four_involutions {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (normal : Subgroup group) [normal.Normal] (odd_normal : Odd (Nat.card normal))
    (first second : Involution group) (distinct : first ≠ second)
    (commutes : Commute first.val second.val) : normal ≤ subgroup := by
  obtain ⟨conjugator, first_mem⟩ := CFSG.OrderReductions.StrongEmbedding.involution_mem_conjugate
    subgroup strong first
  let equivalence := (MulAut.conj conjugator).symm
  let first_conjugate := mapInvolution equivalence.toMonoidHom equivalence.injective first
  let second_conjugate := mapInvolution equivalence.toMonoidHom equivalence.injective second
  have first_conjugate_mem : first_conjugate.val ∈ subgroup := Subgroup.mem_map_equiv.mp first_mem
  have conjugates_distinct : first_conjugate ≠ second_conjugate := by
    intro equal_conjugates
    exact distinct (Subtype.ext (equivalence.injective (congrArg Subtype.val equal_conjugates)))
  have conjugates_commute : Commute first_conjugate.val second_conjugate.val := commutes.map equivalence
  have second_conjugate_mem : second_conjugate.val ∈ subgroup := by
    apply stronglyEmbedded_centralizer_le subgroup strong first_conjugate first_conjugate_mem
    rw [Subgroup.mem_centralizer_iff]
    intro other other_mem
    have other_eq : other = first_conjugate.val := by
      simpa only [Set.mem_singleton_iff] using other_mem
    rw [other_eq]
    exact conjugates_commute.eq
  exact odd_normal_le_of_four_involutions_mem subgroup strong normal odd_normal
    first_conjugate second_conjugate conjugates_distinct conjugates_commute
    first_conjugate_mem second_conjugate_mem

theorem odd_normal_le_normalCore_of_four_involutions {group : Type*}
    [Group group] [Finite group] (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (normal : Subgroup group) [normal.Normal] (odd_normal : Odd (Nat.card normal))
    (first second : Involution group) (distinct : first ≠ second)
    (commutes : Commute first.val second.val) : normal ≤ subgroup.normalCore := by
  have contains := odd_normal_le_of_four_involutions subgroup strong normal odd_normal
    first second distinct commutes
  rw [Subgroup.normalCore_eq_iSup]
  exact le_iSup_of_le normal (le_iSup_of_le (inferInstance : normal.Normal)
    (le_iSup_of_le contains le_rfl))

theorem odd_subgroup_le_of_four_involutions_in_normalizer {group : Type*}
    [Group group] [Finite group] (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (odd_subgroup : Subgroup group) (odd_order : Odd (Nat.card odd_subgroup))
    (first second : Involution (Subgroup.normalizer (odd_subgroup : Set group)))
    (distinct : first ≠ second) (commutes : Commute first.val second.val)
    (involution : Involution group)
    (normalizes : involution.val ∈ Subgroup.normalizer (odd_subgroup : Set group))
    (involution_mem : involution.val ∈ subgroup) : odd_subgroup ≤ subgroup := by
  let normalizer := Subgroup.normalizer (odd_subgroup : Set group)
  by_cases normalizer_le : normalizer ≤ subgroup
  · exact odd_subgroup.le_normalizer.trans normalizer_le
  · have even_intersection : Even (Nat.card ↥(subgroup ⊓ normalizer)) := by
      have divides := Subgroup.orderOf_dvd_natCard (subgroup ⊓ normalizer)
        (show involution.val ∈ subgroup ⊓ normalizer from ⟨involution_mem, normalizes⟩)
      rw [involution.property] at divides
      exact even_iff_two_dvd.mpr divides
    have intersection_strong := CFSG.OrderReductions.StrongEmbeddingInheritance.intersection_stronglyEmbedded
      subgroup strong normalizer normalizer_le even_intersection
    have odd_internal : Odd (Nat.card (odd_subgroup.subgroupOf normalizer)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe odd_subgroup.le_normalizer).toEquiv]
      exact odd_order
    have internal_le := odd_normal_le_of_four_involutions (subgroup.subgroupOf normalizer)
      intersection_strong (odd_subgroup.subgroupOf normalizer) odd_internal
      first second distinct commutes
    intro element element_mem
    exact internal_le (x := ⟨element, odd_subgroup.le_normalizer element_mem⟩) element_mem

end CFSG.OrderReductions.RankTwoContainment
