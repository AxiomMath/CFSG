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
public import CFSG.Assembly.OrderReductions.StrongEmbeddingInheritance
public import CFSG.Assembly.OrderReductions.RankTwoContainment

public section

namespace CFSG.OrderReductions.OddCore

@[expose] def OddNormal {group : Type*} [Group group] (subgroup : Subgroup group) : Prop :=
  subgroup.Normal ∧ Odd (Nat.card subgroup)

theorem odd_sup {group : Type*} [Group group] [Finite group]
    (first second : Subgroup group) [first.Normal]
    (first_odd : Odd (Nat.card first)) (second_odd : Odd (Nat.card second)) :
    Odd (Nat.card ↥(first ⊔ second)) := by
  let projection := QuotientGroup.mk' first
  have image_eq : (first ⊔ second).map projection = second.map projection := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have image_odd : Odd (Nat.card ((first ⊔ second).map projection)) := by
    rw [image_eq]
    exact second_odd.of_dvd_nat (second.card_map_dvd projection)
  have kernel_odd : Odd (Nat.card (projection.ker.subgroupOf (first ⊔ second))) := by
    change Odd (Nat.card ((QuotientGroup.mk' first).ker.subgroupOf (first ⊔ second)))
    rw [QuotientGroup.ker_mk']
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show first ≤ first ⊔ second from le_sup_left)).toEquiv]
    exact first_odd
  have product_odd := image_odd.mul kernel_odd
  rwa [CFSG.OrderReductions.StrongEmbeddingInheritance.map_card_mul_kernel_card projection] at product_odd

theorem exists_greatest_odd_normal {group : Type*} [Group group] [Finite group] :
    ∃ core : Subgroup group, OddNormal core ∧
      ∀ normal : Subgroup group, OddNormal normal → normal ≤ core := by
  have bot_odd_normal : OddNormal (⊥ : Subgroup group) := by
    refine ⟨inferInstance, ?_⟩
    rw [Subgroup.card_bot]
    exact odd_one
  obtain ⟨core, _, maximal⟩ := Finite.exists_le_maximal bot_odd_normal
  refine ⟨core, maximal.prop, ?_⟩
  intro normal normal_prop
  have := maximal.prop.1
  have := normal_prop.1
  have sup_prop : OddNormal (core ⊔ normal) :=
    ⟨inferInstance, odd_sup core normal maximal.prop.2 normal_prop.2⟩
  have equal_sup := maximal.eq_of_le sup_prop le_sup_left
  rw [equal_sup]
  exact le_sup_right

@[expose] noncomputable def oddCore (group : Type*) [Group group] [Finite group] : Subgroup group :=
  Classical.choose (exists_greatest_odd_normal (group := group))

theorem oddCore_odd (group : Type*) [Group group] [Finite group] :
    Odd (Nat.card (oddCore group)) :=
  (Classical.choose_spec (exists_greatest_odd_normal (group := group))).1.2

instance oddCore_normal (group : Type*) [Group group] [Finite group] : (oddCore group).Normal :=
  (Classical.choose_spec (exists_greatest_odd_normal (group := group))).1.1

theorem normal_le_oddCore {group : Type*} [Group group] [Finite group]
    (normal : Subgroup group) [normal.Normal] (odd_normal : Odd (Nat.card normal)) :
    normal ≤ oddCore group :=
  (Classical.choose_spec (exists_greatest_odd_normal (group := group))).2 normal
    ⟨inferInstance, odd_normal⟩

theorem map_oddCore_le_of_surjective {source target : Type*}
    [Group source] [Finite source] [Group target] [Finite target]
    (homomorphism : source →* target) (surjective : Function.Surjective homomorphism) :
    (oddCore source).map homomorphism ≤ oddCore target := by
  have := (inferInstance : (oddCore source).Normal).map homomorphism surjective
  exact normal_le_oddCore _ ((oddCore_odd source).of_dvd_nat
    ((oddCore source).card_map_dvd homomorphism))

theorem map_oddCore_eq_of_equiv {source target : Type*}
    [Group source] [Finite source] [Group target] [Finite target]
    (equivalence : source ≃* target) :
    (oddCore source).map equivalence.toMonoidHom = oddCore target := by
  apply le_antisymm (map_oddCore_le_of_surjective equivalence.toMonoidHom equivalence.surjective)
  have reverse := Subgroup.map_mono (f := equivalence.toMonoidHom)
    (map_oddCore_le_of_surjective equivalence.symm.toMonoidHom equivalence.symm.surjective)
  have composite : equivalence.toMonoidHom.comp equivalence.symm.toMonoidHom =
      MonoidHom.id target := by
    ext element
    exact equivalence.apply_symm_apply element
  rwa [Subgroup.map_map, composite, Subgroup.map_id] at reverse

instance oddCore_characteristic (group : Type*) [Group group] [Finite group] :
    (oddCore group).Characteristic :=
  Subgroup.characteristic_iff_map_eq.mpr map_oddCore_eq_of_equiv

theorem odd_preimage {source target : Type*} [Group source] [Finite source] [Group target]
    (homomorphism : source →* target) (surjective : Function.Surjective homomorphism)
    (odd_kernel : Odd (Nat.card homomorphism.ker))
    (subgroup : Subgroup target) (odd_subgroup : Odd (Nat.card subgroup)) :
    Odd (Nat.card (subgroup.comap homomorphism)) := by
  have image_eq := Subgroup.map_comap_eq_self_of_surjective surjective subgroup
  have image_odd : Odd (Nat.card ((subgroup.comap homomorphism).map homomorphism)) := by
    rwa [image_eq]
  have kernel_le : homomorphism.ker ≤ subgroup.comap homomorphism := by
    intro element element_mem
    change homomorphism element ∈ subgroup
    rw [MonoidHom.mem_ker.mp element_mem]
    exact subgroup.one_mem
  have kernel_odd : Odd (Nat.card (homomorphism.ker.subgroupOf (subgroup.comap homomorphism))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe kernel_le).toEquiv]
    exact odd_kernel
  have product_odd := image_odd.mul kernel_odd
  rwa [CFSG.OrderReductions.StrongEmbeddingInheritance.map_card_mul_kernel_card homomorphism] at product_odd

theorem oddCore_quotient_eq_bot (group : Type*) [Group group] [Finite group] :
    oddCore (group ⧸ oddCore group) = ⊥ := by
  let projection := QuotientGroup.mk' (oddCore group)
  let quotient_core := oddCore (group ⧸ oddCore group)
  let preimage := quotient_core.comap projection
  have : preimage.Normal := (inferInstance : quotient_core.Normal).comap projection
  have kernel_odd : Odd (Nat.card projection.ker) := by
    change Odd (Nat.card (QuotientGroup.mk' (oddCore group)).ker)
    rw [QuotientGroup.ker_mk']
    exact oddCore_odd group
  have preimage_odd : Odd (Nat.card preimage) := odd_preimage projection
    (QuotientGroup.mk'_surjective _) kernel_odd quotient_core (oddCore_odd _)
  have preimage_le := normal_le_oddCore preimage preimage_odd
  have image_le := Subgroup.map_mono (f := projection) preimage_le
  rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
    QuotientGroup.map_mk'_self] at image_le
  exact le_antisymm image_le bot_le

theorem oddCore_eq_normalCore_of_four_involutions {group : Type*}
    [Group group] [Finite group] (subgroup : Subgroup group)
    (strong : CFSG.OrderReductions.InvolutionGraph.StronglyEmbedded subgroup)
    (first second : CFSG.OrderReductions.InvolutionGraph.Involution group) (distinct : first ≠ second)
    (commutes : Commute first.val second.val) : oddCore group = subgroup.normalCore := by
  apply le_antisymm
  · exact CFSG.OrderReductions.RankTwoContainment.odd_normal_le_normalCore_of_four_involutions
      subgroup strong (oddCore group) (oddCore_odd group) first second distinct commutes
  · exact normal_le_oddCore subgroup.normalCore (CFSG.OrderReductions.StrongEmbedding.normalCore_odd subgroup strong)

theorem characteristic_subgroup_map_normal {group : Type*} [Group group]
    (normal : Subgroup group) [normal.Normal]
    (characteristic : Subgroup normal) [characteristic.Characteristic] :
    (characteristic.map normal.subtype).Normal := by
  constructor
  intro element mem_image conjugator
  obtain ⟨original, original_mem, image_eq⟩ := Subgroup.mem_map.mp mem_image
  let automorphism : MulAut normal := MulAut.conjNormal conjugator
  have invariant : characteristic.map automorphism.toMonoidHom = characteristic :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance automorphism
  have moved_mem : automorphism original ∈ characteristic := by
    rw [← invariant]
    exact Subgroup.mem_map_of_mem automorphism.toMonoidHom original_mem
  refine Subgroup.mem_map.mpr ⟨automorphism original, moved_mem, ?_⟩
  change ((MulAut.conjNormal conjugator) original).val = conjugator * element * conjugator⁻¹
  rw [MulAut.conjNormal_apply]
  change conjugator * normal.subtype original * conjugator⁻¹ = conjugator * element * conjugator⁻¹
  rw [image_eq]

theorem normal_subgroup_oddCore_map_le {group : Type*} [Group group] [Finite group]
    (normal : Subgroup group) [normal.Normal] :
    (oddCore normal).map normal.subtype ≤ oddCore group := by
  have : ((oddCore normal).map normal.subtype).Normal :=
    characteristic_subgroup_map_normal normal (oddCore normal)
  apply normal_le_oddCore
  rw [Subgroup.card_map_of_injective Subtype.val_injective]
  exact oddCore_odd normal

theorem normal_subgroup_oddCore_eq_bot {group : Type*} [Group group] [Finite group]
    (core_bot : oddCore group = ⊥) (normal : Subgroup group) [normal.Normal] :
    oddCore normal = ⊥ := by
  have image_le := normal_subgroup_oddCore_map_le normal
  rw [core_bot] at image_le
  apply Subgroup.map_injective (f := normal.subtype) Subtype.val_injective
  exact (le_antisymm image_le bot_le).trans (Subgroup.map_bot _).symm

theorem oddCore_preimage_eq_of_odd_kernel {source target : Type*}
    [Group source] [Finite source] [Group target] [Finite target]
    (homomorphism : source →* target) (surjective : Function.Surjective homomorphism)
    (odd_kernel : Odd (Nat.card homomorphism.ker)) :
    (oddCore target).comap homomorphism = oddCore source := by
  apply le_antisymm
  · have : ((oddCore target).comap homomorphism).Normal :=
      (inferInstance : (oddCore target).Normal).comap homomorphism
    exact normal_le_oddCore _ (odd_preimage homomorphism surjective odd_kernel _ (oddCore_odd target))
  · exact Subgroup.map_le_iff_le_comap.mp (map_oddCore_le_of_surjective homomorphism surjective)

theorem oddCore_image_eq_of_odd_kernel {source target : Type*}
    [Group source] [Finite source] [Group target] [Finite target]
    (homomorphism : source →* target) (surjective : Function.Surjective homomorphism)
    (odd_kernel : Odd (Nat.card homomorphism.ker)) :
    (oddCore source).map homomorphism = oddCore target := by
  rw [← oddCore_preimage_eq_of_odd_kernel homomorphism surjective odd_kernel,
    Subgroup.map_comap_eq_self_of_surjective surjective]

end CFSG.OrderReductions.OddCore
