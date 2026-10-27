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
public import CFSG.Assembly.OrderReductions.StrongEmbedding

public section

namespace CFSG.OrderReductions.StrongEmbeddingInheritance

open CFSG.OrderReductions.InvolutionGraph

theorem intersection_stronglyEmbedded {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (ambient : Subgroup group) (not_contains : ¬ ambient ≤ subgroup)
    (even_intersection : Even (Nat.card ↥(subgroup ⊓ ambient))) :
    StronglyEmbedded (subgroup.subgroupOf ambient) := by
  have proper : subgroup.subgroupOf ambient ≠ ⊤ := by
    intro equal_top
    exact not_contains (Subgroup.subgroupOf_eq_top.mp equal_top)
  have even_internal : Even (Nat.card (subgroup.subgroupOf ambient)) := by
    have equal_card := Subgroup.card_map_of_injective
      (K := subgroup.subgroupOf ambient) (f := ambient.subtype) Subtype.val_injective
    rw [Subgroup.subgroupOf_map_subtype] at equal_card
    rwa [← equal_card]
  refine ⟨proper, even_internal, ?_⟩
  intro conjugator not_mem
  have outside : conjugator.val ∉ subgroup := fun mem_subgroup =>
    not_mem (Subgroup.mem_subgroupOf.mpr mem_subgroup)
  let intersection := subgroup.subgroupOf ambient ⊓
    (subgroup.subgroupOf ambient).map (MulAut.conj conjugator).toMonoidHom
  have image_le : intersection.map ambient.subtype ≤
      subgroup ⊓ subgroup.map (MulAut.conj conjugator.val).toMonoidHom := by
    intro element mem_image
    obtain ⟨preimage, mem_internal, equal_image⟩ := Subgroup.mem_map.mp mem_image
    rw [← equal_image]
    refine ⟨Subgroup.mem_subgroupOf.mp mem_internal.1, ?_⟩
    obtain ⟨original, mem_original, equal_conjugate⟩ := Subgroup.mem_map.mp mem_internal.2
    refine Subgroup.mem_map.mpr ⟨original.val, Subgroup.mem_subgroupOf.mp mem_original, ?_⟩
    exact congrArg Subtype.val equal_conjugate
  have divides := (Subgroup.card_dvd_of_le image_le)
  rw [Subgroup.card_map_of_injective Subtype.val_injective] at divides
  exact (strong.2.2 conjugator.val outside).of_dvd_nat divides

theorem map_inf_of_ker_le {source target : Type*} [Group source] [Group target]
    (homomorphism : source →* target) (first second : Subgroup source)
    (kernel_le_first : homomorphism.ker ≤ first) :
    (first ⊓ second).map homomorphism = first.map homomorphism ⊓ second.map homomorphism := by
  apply le_antisymm (Subgroup.map_inf_le _ _ _)
  intro element mem_intersection
  obtain ⟨first_element, first_mem, first_image⟩ := Subgroup.mem_map.mp mem_intersection.1
  obtain ⟨second_element, second_mem, second_image⟩ := Subgroup.mem_map.mp mem_intersection.2
  have product_kernel : first_element⁻¹ * second_element ∈ homomorphism.ker := by
    change homomorphism (first_element⁻¹ * second_element) = 1
    rw [map_mul, map_inv, first_image, second_image, inv_mul_cancel]
  have second_mem_first : second_element ∈ first := by
    have product_mem := first.mul_mem first_mem (kernel_le_first product_kernel)
    rwa [← mul_assoc, mul_inv_cancel, one_mul] at product_mem
  exact Subgroup.mem_map.mpr ⟨second_element, ⟨second_mem_first, second_mem⟩, second_image⟩

theorem map_conjugate {source target : Type*} [Group source] [Group target]
    (homomorphism : source →* target) (subgroup : Subgroup source) (conjugator : source) :
    (subgroup.map (MulAut.conj conjugator).toMonoidHom).map homomorphism =
      (subgroup.map homomorphism).map (MulAut.conj (homomorphism conjugator)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext element
  change homomorphism (conjugator * element * conjugator⁻¹) =
    homomorphism conjugator * homomorphism element * (homomorphism conjugator)⁻¹
  rw [map_mul, map_mul, map_inv]

theorem map_card_mul_kernel_card {source target : Type*} [Group source] [Group target]
    (homomorphism : source →* target) (subgroup : Subgroup source) :
    Nat.card (subgroup.map homomorphism) * Nat.card (homomorphism.ker.subgroupOf subgroup) =
      Nat.card subgroup := by
  let restriction := homomorphism.domRestrict subgroup
  have kernel_eq : restriction.ker = homomorphism.ker.subgroupOf subgroup := rfl
  have range_eq : restriction.range = subgroup.map homomorphism := MonoidHom.domRestrict_range _ _
  have quotient_card := Nat.card_congr (QuotientGroup.quotientKerEquivRange restriction).toEquiv
  have product_eq := restriction.ker.card_eq_card_quotient_mul_card_subgroup
  rw [quotient_card, kernel_eq, range_eq] at product_eq
  exact product_eq.symm

theorem surjective_odd_kernel_stronglyEmbedded {source target : Type*} [Group source]
    [Finite source] [Group target] (homomorphism : source →* target)
    (surjective : Function.Surjective homomorphism)
    (subgroup : Subgroup source) (strong : StronglyEmbedded subgroup)
    (kernel_le : homomorphism.ker ≤ subgroup) (odd_kernel : Odd (Nat.card homomorphism.ker)) :
    StronglyEmbedded (subgroup.map homomorphism) := by
  have proper : subgroup.map homomorphism ≠ ⊤ := by
    intro equal_top
    have preimage_eq := Subgroup.comap_map_eq_self kernel_le
    rw [equal_top, Subgroup.comap_top] at preimage_eq
    exact strong.1 preimage_eq.symm
  have image_even : Even (Nat.card (subgroup.map homomorphism)) := by
    have kernel_card_eq := Nat.card_congr (Subgroup.subgroupOfEquivOfLe kernel_le).toEquiv
    have product_eq := map_card_mul_kernel_card homomorphism subgroup
    rw [kernel_card_eq] at product_eq
    by_contra not_even
    have product_odd := (Nat.not_even_iff_odd.mp not_even).mul odd_kernel
    rw [product_eq] at product_odd
    exact product_odd.not_two_dvd_nat strong.2.1.two_dvd
  refine ⟨proper, image_even, ?_⟩
  intro conjugator not_mem
  obtain ⟨preimage, equal_conjugator⟩ := surjective conjugator
  have outside : preimage ∉ subgroup := by
    intro mem_subgroup
    exact not_mem (equal_conjugator ▸ Subgroup.mem_map_of_mem homomorphism mem_subgroup)
  have odd_intersection := strong.2.2 preimage outside
  have odd_image := odd_intersection.of_dvd_nat
    ((subgroup ⊓ subgroup.map (MulAut.conj preimage).toMonoidHom).card_map_dvd homomorphism)
  rw [map_inf_of_ker_le homomorphism subgroup _ kernel_le, map_conjugate,
    equal_conjugator] at odd_image
  exact odd_image

theorem odd_normal_quotient_stronglyEmbedded {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (strong : StronglyEmbedded subgroup)
    (kernel : Subgroup group) [kernel.Normal] (kernel_le : kernel ≤ subgroup)
    (odd_kernel : Odd (Nat.card kernel)) :
    StronglyEmbedded (subgroup.map (QuotientGroup.mk' kernel)) := by
  apply surjective_odd_kernel_stronglyEmbedded (QuotientGroup.mk' kernel)
    (QuotientGroup.mk'_surjective kernel) subgroup strong
  · simpa only [QuotientGroup.ker_mk'] using kernel_le
  · simpa only [QuotientGroup.ker_mk'] using odd_kernel

@[expose] def conjugatesMap {source target : Type*} [Group source] [Group target]
    (homomorphism : source →* target) (subgroup : Subgroup source) :
    CFSG.OrderReductions.StrongEmbedding.Conjugates subgroup →
      CFSG.OrderReductions.StrongEmbedding.Conjugates (subgroup.map homomorphism) := fun conjugate =>
  ⟨conjugate.val.map homomorphism, by
    obtain ⟨conjugator, conjugates⟩ := conjugate.property
    change conjugator • subgroup = conjugate.val at conjugates
    refine ⟨homomorphism conjugator, ?_⟩
    change homomorphism conjugator • subgroup.map homomorphism = conjugate.val.map homomorphism
    rw [← conjugates, CFSG.OrderReductions.StrongEmbedding.subgroup_smul,
      CFSG.OrderReductions.StrongEmbedding.subgroup_smul, map_conjugate]⟩

theorem conjugatesMap_equivariant {source target : Type*} [Group source] [Group target]
    (homomorphism : source →* target) (subgroup : Subgroup source) (conjugator : source)
    (conjugate : CFSG.OrderReductions.StrongEmbedding.Conjugates subgroup) :
    conjugatesMap homomorphism subgroup (conjugator • conjugate) =
      homomorphism conjugator • conjugatesMap homomorphism subgroup conjugate := by
  apply Subtype.ext
  change (conjugator • conjugate.val).map homomorphism =
    homomorphism conjugator • conjugate.val.map homomorphism
  rw [CFSG.OrderReductions.StrongEmbedding.subgroup_smul, CFSG.OrderReductions.StrongEmbedding.subgroup_smul,
    map_conjugate]

theorem kernel_le_conjugate {source target : Type*} [Group source] [Group target]
    (homomorphism : source →* target) (subgroup : Subgroup source)
    (kernel_le : homomorphism.ker ≤ subgroup)
    (conjugate : CFSG.OrderReductions.StrongEmbedding.Conjugates subgroup) :
    homomorphism.ker ≤ conjugate.val := by
  obtain ⟨conjugator, conjugates⟩ := conjugate.property
  change conjugator • subgroup = conjugate.val at conjugates
  rw [← conjugates, CFSG.OrderReductions.StrongEmbedding.subgroup_smul, Subgroup.map_equiv_eq_comap_symm']
  intro element mem_kernel
  apply kernel_le
  change homomorphism (conjugator⁻¹ * element * conjugator) = 1
  rw [map_mul, map_mul, map_inv, mem_kernel, mul_one, inv_mul_cancel]

theorem conjugatesMap_bijective {source target : Type*} [Group source] [Group target]
    (homomorphism : source →* target) (surjective : Function.Surjective homomorphism)
    (subgroup : Subgroup source) (kernel_le : homomorphism.ker ≤ subgroup) :
    Function.Bijective (conjugatesMap homomorphism subgroup) := by
  constructor
  · intro first second equal_images
    apply Subtype.ext
    apply Subgroup.map_injective_of_ker_le homomorphism
      (kernel_le_conjugate homomorphism subgroup kernel_le first)
      (kernel_le_conjugate homomorphism subgroup kernel_le second)
    exact congrArg Subtype.val equal_images
  · intro conjugate
    obtain ⟨conjugator, conjugates⟩ := conjugate.property
    change conjugator • subgroup.map homomorphism = conjugate.val at conjugates
    obtain ⟨preimage, equal_conjugator⟩ := surjective conjugator
    refine ⟨⟨preimage • subgroup, ⟨preimage, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change (preimage • subgroup).map homomorphism = conjugate.val
    rw [CFSG.OrderReductions.StrongEmbedding.subgroup_smul, map_conjugate,
      equal_conjugator, ← CFSG.OrderReductions.StrongEmbedding.subgroup_smul, conjugates]

@[expose] noncomputable def conjugatesEquiv {source target : Type*} [Group source] [Group target]
    (homomorphism : source →* target) (surjective : Function.Surjective homomorphism)
    (subgroup : Subgroup source) (kernel_le : homomorphism.ker ≤ subgroup) :
    CFSG.OrderReductions.StrongEmbedding.Conjugates subgroup ≃
      CFSG.OrderReductions.StrongEmbedding.Conjugates (subgroup.map homomorphism) :=
  Equiv.ofBijective (conjugatesMap homomorphism subgroup)
    (conjugatesMap_bijective homomorphism surjective subgroup kernel_le)

theorem equivariant_bijective_two_pretransitive_iff {source target first_points second_points : Type*}
    [Group source] [Group target] [MulAction source first_points] [MulAction target second_points]
    (homomorphism : source →* target) (surjective : Function.Surjective homomorphism)
    (equivalence : first_points ≃ second_points)
    (equivariant : ∀ element : source, ∀ point : first_points,
      equivalence (element • point) = homomorphism element • equivalence point) :
    MulAction.IsMultiplyPretransitive source first_points 2 ↔
      MulAction.IsMultiplyPretransitive target second_points 2 := by
  rw [MulAction.is_two_pretransitive_iff, MulAction.is_two_pretransitive_iff]
  constructor
  · intro transitive first second third fourth first_distinct third_distinct
    obtain ⟨element, first_moves, second_moves⟩ := transitive
      (fun equal => first_distinct (equivalence.symm.injective equal))
      (fun equal => third_distinct (equivalence.symm.injective equal))
    refine ⟨homomorphism element, ?_, ?_⟩
    · have mapped := congrArg equivalence first_moves
      simpa only [equivariant, Equiv.apply_symm_apply] using mapped
    · have mapped := congrArg equivalence second_moves
      simpa only [equivariant, Equiv.apply_symm_apply] using mapped
  · intro transitive first second third fourth first_distinct third_distinct
    obtain ⟨element, first_moves, second_moves⟩ := transitive
      (fun equal => first_distinct (equivalence.injective equal))
      (fun equal => third_distinct (equivalence.injective equal))
    obtain ⟨preimage, maps_element⟩ := surjective element
    refine ⟨preimage, ?_, ?_⟩
    · apply equivalence.injective
      rw [equivariant, maps_element]
      exact first_moves
    · apply equivalence.injective
      rw [equivariant, maps_element]
      exact second_moves

theorem conjugates_two_pretransitive_iff {source target : Type*} [Group source] [Group target]
    (homomorphism : source →* target) (surjective : Function.Surjective homomorphism)
    (subgroup : Subgroup source) (kernel_le : homomorphism.ker ≤ subgroup) :
    MulAction.IsMultiplyPretransitive source (CFSG.OrderReductions.StrongEmbedding.Conjugates subgroup) 2 ↔
      MulAction.IsMultiplyPretransitive target
        (CFSG.OrderReductions.StrongEmbedding.Conjugates (subgroup.map homomorphism)) 2 := by
  exact equivariant_bijective_two_pretransitive_iff homomorphism surjective
    (conjugatesEquiv homomorphism surjective subgroup kernel_le)
    (conjugatesMap_equivariant homomorphism subgroup)

end CFSG.OrderReductions.StrongEmbeddingInheritance
