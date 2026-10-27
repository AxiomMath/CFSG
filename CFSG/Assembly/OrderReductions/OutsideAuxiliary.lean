module

public import CFSG.Assembly.OrderReductions.OutsideCentralizer
public import CFSG.Assembly.OrderReductions.SolvableMaximal

public section

namespace CFSG.OrderReductions.OutsideAuxiliary

open CFSG.OrderReductions.InvolutionGraph
open CFSG.OrderReductions.NormalizerAuxiliary

theorem solvable_normalized_cyclic_sup {group : Type*} [Group group]
    (normal cyclic : Subgroup group) [Group.IsSolvable normal] [IsCyclic cyclic]
    (normalizes : cyclic ≤ Subgroup.normalizer (normal : Set group)) :
    Group.IsSolvable ↥(normal ⊔ cyclic) := by
  let ambient := normal ⊔ cyclic
  let kernel := normal.subgroupOf ambient
  let complement := cyclic.subgroupOf ambient
  have : kernel.Normal := by
    change (normal.subgroupOf (normal ⊔ cyclic)).Normal
    rw [sup_comm]
    exact Subgroup.normal_subgroupOf_sup_of_le_normalizer normalizes
  have : Group.IsSolvable kernel :=
    Group.isSolvable_of_surjective (f :=
      (Subgroup.subgroupOfEquivOfLe (show normal ≤ ambient from le_sup_left)).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (show normal ≤ ambient from le_sup_left)).symm.surjective
  have : IsCyclic complement :=
    isCyclic_of_surjective
      (Subgroup.subgroupOfEquivOfLe (show cyclic ≤ ambient from le_sup_right)).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe (show cyclic ≤ ambient from le_sup_right)).symm.surjective
  have : Group.IsSolvable complement :=
    Group.isSolvable_of_comm (isMulCommutative_iff.mp inferInstance)
  let projection := QuotientGroup.mk' kernel
  have generates : kernel ⊔ complement = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self ambient
  have image_top : complement.map projection = ⊤ := by
    have image_sup := congrArg (Subgroup.map projection) generates
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective kernel)] at image_sup
    exact image_sup
  have surjective : Function.Surjective (projection.comp complement.subtype) := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, Subgroup.subtype_range]
    exact image_top
  have : Group.IsSolvable (ambient ⧸ kernel) := Group.isSolvable_of_surjective surjective
  exact (Group.isSolvable_iff_subgroup_quotient kernel).mpr ⟨inferInstance, inferInstance⟩

theorem exists_minimal_extension {group : Type*} [Group group] [Finite group]
    (subgroup ambient : Subgroup group) (strict : subgroup < ambient) :
    ∃ extension : Subgroup group, subgroup < extension ∧ extension ≤ ambient ∧
      IsCoatom (subgroup.subgroupOf extension) := by
  obtain ⟨extension, extension_le, minimal⟩ := Finite.exists_le_minimal
    (p := fun larger : Subgroup group => subgroup < larger) strict
  have subgroup_le : subgroup ≤ extension := minimal.prop.le
  refine ⟨extension, minimal.prop, extension_le, ?_⟩
  constructor
  · intro equal_top
    exact minimal.prop.ne (le_antisymm subgroup_le (Subgroup.subgroupOf_eq_top.mp equal_top))
  · intro larger strict_larger
    have image_strict : subgroup < larger.map extension.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le subgroup_le]
      exact (Subgroup.map_lt_map_iff_of_injective Subtype.val_injective).mpr strict_larger
    have image_eq := minimal.eq_of_le image_strict (Subgroup.map_subtype_le larger)
    apply Subgroup.map_injective (f := extension.subtype) Subtype.val_injective
    rw [← MonoidHom.range_eq_map, Subgroup.subtype_range]
    exact image_eq

theorem conjugator_in_odd_normal_part {group : Type*} [Group group] [Finite group]
    (ambient : Subgroup group) (strong : StronglyEmbedded ambient)
    (normal : Subgroup group) (involution : Involution group)
    (mem_ambient : involution.val ∈ ambient)
    (normalizes : involution.val ∈ Subgroup.normalizer (normal : Set group))
    (crosses : ¬ normal ≤ ambient)
    (outside : Involution group) (outside_mem : outside.val ∈ normal ⊔ Subgroup.zpowers involution.val) :
    ∃ conjugator ∈ normal, conjugator • involution = outside := by
  let overgroup := normal ⊔ Subgroup.zpowers involution.val
  have involution_mem : involution.val ∈ overgroup :=
    (show Subgroup.zpowers involution.val ≤ overgroup from le_sup_right) (Subgroup.mem_zpowers _)
  have overgroup_crosses : ¬ overgroup ≤ ambient := fun contains => crosses (le_sup_left.trans contains)
  have even_intersection : Even (Nat.card ↥(ambient ⊓ overgroup)) := by
    apply even_iff_two_dvd.mpr
    have divides := Subgroup.orderOf_dvd_natCard (ambient ⊓ overgroup) ⟨mem_ambient, involution_mem⟩
    rwa [involution.property] at divides
  have strong_internal := CFSG.OrderReductions.StrongEmbeddingInheritance.intersection_stronglyEmbedded
    ambient strong overgroup overgroup_crosses even_intersection
  let first : Involution overgroup :=
    ⟨⟨involution.val, involution_mem⟩, by rw [← Subgroup.orderOf_coe]; exact involution.property⟩
  let second : Involution overgroup :=
    ⟨⟨outside.val, outside_mem⟩, by rw [← Subgroup.orderOf_coe]; exact outside.property⟩
  obtain ⟨acting, conjugates⟩ := CFSG.OrderReductions.InvolutionFusion.all_involutions_conjugate_of_disconnected
    (stronglyEmbedded_not_preconnected _ strong_internal) first second
  have cyclic_normalizes : Subgroup.zpowers involution.val ≤ Subgroup.normalizer (normal : Set group) :=
    Subgroup.zpowers_le.mpr normalizes
  have : (normal.subgroupOf overgroup).Normal := by
    change (normal.subgroupOf (normal ⊔ Subgroup.zpowers involution.val)).Normal
    rw [sup_comm]
    exact Subgroup.normal_subgroupOf_sup_of_le_normalizer cyclic_normalizes
  have generates : normal.subgroupOf overgroup ⊔ (Subgroup.zpowers involution.val).subgroupOf overgroup = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self overgroup
  obtain ⟨first_part, first_mem, second_part, second_mem, product_eq⟩ :=
    Subgroup.mem_sup_of_normal_left.mp (generates ▸ Subgroup.mem_top acting)
  have second_fixes : second_part.val • involution = involution := by
    have cyclic_centralizes : Subgroup.zpowers involution.val ≤
        Subgroup.centralizer ({involution.val} : Set group) := by
      apply Subgroup.zpowers_le.mpr
      apply Subgroup.mem_centralizer_iff.mpr
      intro other other_mem
      have other_eq : other = involution.val := by simpa using other_mem
      rw [other_eq]
    have fixes := cyclic_centralizes second_mem
    rwa [← involution_stabilizer_eq_centralizer, MulAction.mem_stabilizer_iff] at fixes
  refine ⟨first_part.val, first_mem, ?_⟩
  have conjugates_values : acting.val • involution = outside := by
    apply Subtype.ext
    exact congrArg (fun vertex : Involution overgroup => vertex.val.val) conjugates
  rw [← product_eq] at conjugates_values
  change (first_part.val * second_part.val) • involution = outside at conjugates_values
  rwa [mul_smul, second_fixes] at conjugates_values

theorem internal_maximal_intersection_le_point {group : Type*} [Group group] [Finite group]
    (point : Component group)
    (extension : Subgroup group) [Group.IsSolvable extension]
    (strong_internal : StronglyEmbedded ((componentStabilizer point).subgroupOf extension))
    (maximal : IsCoatom ((componentStabilizer point).subgroupOf extension))
    (inside outside : Involution group) (inside_mem : inside.val ∈ componentStabilizer point)
    (inside_extension : inside.val ∈ extension) (outside_extension : outside.val ∈ extension)
    (outside_not_mem : outside.val ∉ componentStabilizer point) :
    componentStabilizer point ⊓ extension ⊓
      (componentStabilizer point).map (MulAut.conj outside.val).toMonoidHom ≤
        componentStabilizer ((commutingGraph group).connectedComponentMk outside) := by
  let internal_subgroup := (componentStabilizer point).subgroupOf extension
  let first : Involution extension :=
    ⟨⟨inside.val, inside_extension⟩, by rw [← Subgroup.orderOf_coe]; exact inside.property⟩
  let second : Involution extension :=
    ⟨⟨outside.val, outside_extension⟩, by rw [← Subgroup.orderOf_coe]; exact outside.property⟩
  obtain ⟨conjugator, conjugates⟩ := CFSG.OrderReductions.InvolutionFusion.all_involutions_conjugate_of_disconnected
    (stronglyEmbedded_not_preconnected internal_subgroup strong_internal) first second
  have conjugates_ambient : conjugator.val • inside = outside := by
    apply Subtype.ext
    exact congrArg (fun vertex : Involution extension => vertex.val.val) conjugates
  have internal_mem : second.val ∈ internal_subgroup.map (MulAut.conj conjugator).toMonoidHom := by
    apply Subgroup.mem_map.mpr
    refine ⟨first.val, inside_mem, ?_⟩
    exact congrArg Subtype.val conjugates
  have identity := CFSG.OrderReductions.SolvableMaximal.maximal_pair_intersection internal_subgroup strong_internal
    maximal second outside_not_mem conjugator internal_mem
  have image_le := Subgroup.map_mono (f := extension.subtype)
    (show internal_subgroup ⊓ internal_subgroup.map (MulAut.conj second.val).toMonoidHom ≤
      internal_subgroup.map (MulAut.conj conjugator).toMonoidHom from identity ▸ inf_le_right)
  rw [Subgroup.map_inf _ _ _ Subtype.val_injective,
    CFSG.OrderReductions.StrongEmbeddingInheritance.map_conjugate,
    CFSG.OrderReductions.StrongEmbeddingInheritance.map_conjugate,
    Subgroup.subgroupOf_map_subtype] at image_le
  have moved_eq := component_smul_of_conjugates point inside outside inside_mem conjugator.val conjugates_ambient
  have conjugate_le : (componentStabilizer point ⊓ extension).map
      (MulAut.conj conjugator.val).toMonoidHom ≤
        componentStabilizer ((commutingGraph group).connectedComponentMk outside) := by
    have contains := Subgroup.map_mono (f := (MulAut.conj conjugator.val).toMonoidHom)
      (show componentStabilizer point ⊓ extension ≤ componentStabilizer point from inf_le_left)
    rwa [← componentStabilizer_smul, moved_eq] at contains
  intro element element_mem
  apply conjugate_le
  apply image_le
  refine ⟨element_mem.1, Subgroup.mem_map.mpr ?_⟩
  have reflected_mem := Subgroup.mem_map_equiv.mp element_mem.2
  refine ⟨(MulAut.conj outside.val).symm element, ⟨reflected_mem, ?_⟩,
    (MulAut.conj outside.val).apply_symm_apply element⟩
  change outside.val⁻¹ * element * outside.val ∈ extension
  exact extension.mul_mem (extension.mul_mem (extension.inv_mem outside_extension) element_mem.1.2)
    outside_extension

theorem outside_centralizer_auxiliary_of_solvable {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (point : Component group)
    (strong : StronglyEmbedded (componentStabilizer point))
    (prime_subgroup : Subgroup group) (prime_group : IsPGroup prime prime_subgroup)
    (contains : prime_subgroup ≤ componentStabilizer point)
    (inside : Involution group) (inside_mem : inside.val ∈ componentStabilizer point)
    (normalizes : inside.val ∈ Subgroup.normalizer (prime_subgroup : Set group))
    (crosses : ¬ Subgroup.centralizer (inversionSet prime_subgroup inside) ≤ componentStabilizer point)
    [Group.IsSolvable (Subgroup.centralizer (inversionSet prime_subgroup inside))] :
    ∃ extension : Subgroup group,
      AuxiliaryData point (inversionSet prime_subgroup inside) inside prime extension := by
  let elements := inversionSet prime_subgroup inside
  let centralizer := Subgroup.centralizer elements
  let overgroup := centralizer ⊔ Subgroup.zpowers inside.val
  let intersection := componentStabilizer point ⊓ overgroup
  have inside_overgroup : inside.val ∈ overgroup :=
    (show Subgroup.zpowers inside.val ≤ overgroup from le_sup_right) (Subgroup.mem_zpowers _)
  have inside_intersection : inside.val ∈ intersection := ⟨inside_mem, inside_overgroup⟩
  have overgroup_crosses : ¬ overgroup ≤ componentStabilizer point :=
    fun contained => crosses (le_sup_left.trans contained)
  have intersection_strict : intersection < overgroup := by
    apply lt_of_le_of_ne inf_le_right
    intro equal
    exact overgroup_crosses (equal ▸ inf_le_left)
  obtain ⟨extension, extension_strict, extension_le, maximal⟩ :=
    exists_minimal_extension intersection overgroup intersection_strict
  have intersection_eq : componentStabilizer point ⊓ extension = intersection :=
    le_antisymm (inf_le_inf_left _ extension_le) (le_inf inf_le_left extension_strict.le)
  have point_internal_eq : (componentStabilizer point).subgroupOf extension = intersection.subgroupOf extension := by
    apply Subgroup.map_injective (f := extension.subtype) Subtype.val_injective
    rw [Subgroup.subgroupOf_map_subtype, intersection_eq,
      Subgroup.map_subgroupOf_eq_of_le extension_strict.le]
  have inside_extension := extension_strict.le inside_intersection
  have extension_crosses : ¬ extension ≤ componentStabilizer point := by
    intro contained
    have extension_le_intersection : extension ≤ intersection := le_inf contained extension_le
    exact extension_strict.not_ge extension_le_intersection
  have even_intersection : Even (Nat.card ↥(componentStabilizer point ⊓ extension)) := by
    apply even_iff_two_dvd.mpr
    have divides := Subgroup.orderOf_dvd_natCard (componentStabilizer point ⊓ extension)
      ⟨inside_mem, inside_extension⟩
    rwa [inside.property] at divides
  have strong_internal := CFSG.OrderReductions.StrongEmbeddingInheritance.intersection_stronglyEmbedded
    (componentStabilizer point) strong extension extension_crosses even_intersection
  have point_maximal : IsCoatom ((componentStabilizer point).subgroupOf extension) :=
    point_internal_eq.symm ▸ maximal
  have cyclic_normalizes : Subgroup.zpowers inside.val ≤ Subgroup.normalizer (centralizer : Set group) :=
    Subgroup.zpowers_le.mpr
      (CFSG.OrderReductions.OutsideCentralizer.involution_normalizes_centralizer prime_subgroup inside normalizes)
  have : Group.IsSolvable overgroup := solvable_normalized_cyclic_sup centralizer _ cyclic_normalizes
  have : Group.IsSolvable extension := by
    have : Group.IsSolvable (extension.subgroupOf overgroup) := inferInstance
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe extension_le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe extension_le).surjective
  refine ⟨extension, inside_extension, strong_internal, ?_⟩
  intro outside outside_extension outside_not_mem
  obtain ⟨conjugator, conjugator_mem, conjugates⟩ := conjugator_in_odd_normal_part
    (componentStabilizer point) strong centralizer inside inside_mem
    (CFSG.OrderReductions.OutsideCentralizer.involution_normalizes_centralizer prime_subgroup inside normalizes)
    crosses outside (extension_le outside_extension)
  have outside_point : (commutingGraph group).connectedComponentMk outside ≠ point := by
    intro equal
    exact outside_not_mem ((componentStabilizer_involution_iff point outside).mpr equal)
  have elements_fixed : ∀ element ∈ elements, (MulAut.conj conjugator) element = element := by
    intro element element_mem
    have commuting := Subgroup.mem_centralizer_iff.mp conjugator_mem element element_mem
    change conjugator * element * conjugator⁻¹ = element
    rw [← commuting, mul_assoc, mul_inv_cancel, mul_one]
  have elements_point : elements ⊆ componentStabilizer ((commutingGraph group).connectedComponentMk outside) := by
    intro element element_mem
    have moved_eq := component_smul_of_conjugates point inside outside inside_mem conjugator conjugates
    rw [← moved_eq, componentStabilizer_smul]
    exact Subgroup.mem_map.mpr ⟨element, contains element_mem.1, elements_fixed element element_mem⟩
  have elements_inverted : ∀ element ∈ elements, (MulAut.conj outside.val) element = element⁻¹ := by
    intro element element_mem
    have intertwined := congrArg (fun automorphism : MulAut group => automorphism element)
      (conjugation_intertwines inside outside conjugator conjugates)
    change (MulAut.conj outside.val) ((MulAut.conj conjugator) element) =
      (MulAut.conj conjugator) ((MulAut.conj inside.val) element) at intertwined
    rw [elements_fixed element element_mem, element_mem.2, map_inv, elements_fixed element element_mem] at intertwined
    exact intertwined
  let generated := Subgroup.closure elements
  have generated_le : generated ≤ prime_subgroup := (Subgroup.closure_le _).mpr fun element element_mem => element_mem.1
  have generated_pair : generated ≤ CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup
      ((commutingGraph group).connectedComponentMk outside) point := by
    apply (Subgroup.closure_le _).mpr
    intro element element_mem
    exact ⟨elements_point element_mem, contains element_mem.1⟩
  have centralizer_pair : centralizer ⊓ CFSG.OrderReductions.InvolutiveIntersection.intersection
      (MulAut.conj outside.val) (componentStabilizer point) ≤
        componentStabilizer ((commutingGraph group).connectedComponentMk outside) := by
    intro element element_mem
    apply internal_maximal_intersection_le_point point extension strong_internal point_maximal
      inside outside inside_mem inside_extension outside_extension outside_not_mem
    refine ⟨⟨element_mem.2.1, extension_strict.le ?_⟩, element_mem.2.2⟩
    exact ⟨element_mem.2.1, (show centralizer ≤ overgroup from le_sup_left) element_mem.1⟩
  refine ⟨elements_point, ?_⟩
  exact CFSG.OrderReductions.OddPrimeCoreTransfer.component_three_point_core_transfer prime
    ((commutingGraph group).connectedComponentMk outside) point outside_point outside
    (involution_mem_componentStabilizer outside) elements generated rfl
    (prime_group.to_le generated_le) generated_pair elements_inverted centralizer_pair

end CFSG.OrderReductions.OutsideAuxiliary
