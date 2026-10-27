module

public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents

public section

open CFSG.Open

namespace CFSG.ComponentClassification.OrdinaryComponentTransport

theorem subgroupOf_subtype_map {G : Type*} [Group G]
    (overgroup : Subgroup G) (component : Subgroup overgroup) :
    (component.map overgroup.subtype).subgroupOf overgroup = component := by
  ext member
  constructor
  · rintro ⟨lift, hlift, heq⟩
    rwa [show lift = member from Subtype.ext heq] at hlift
  · intro hmember
    exact Subgroup.mem_map_of_mem overgroup.subtype hmember

theorem subtype_image_component {G : Type*} [Group G]
    (overgroup : Subgroup G) (component : Subgroup overgroup)
    (hcomponent : IsComponentOf component ⊤) :
    IsComponentOf ((component.map overgroup.subtype).subgroupOf overgroup) ⊤ := by
  rwa [subgroupOf_subtype_map]

theorem subgroupOf_iff {G : Type*} [Group G]
    (component overgroup : Subgroup G) (hle : component ≤ overgroup) :
    IsComponentOf (component.subgroupOf overgroup) ⊤ ↔
      (component.subgroupOf overgroup).IsSubnormal ∧ IsQuasisimple component := by
  let equivalence := Subgroup.subgroupOfEquivOfLe hle
  constructor
  · intro hcomponent
    exact ⟨Components.mathlib_subnormal_of_chain hcomponent.2.1 Subgroup.IsSubnormal.top,
      Components.quasisimple_of_equiv equivalence.symm hcomponent.2.2⟩
  · rintro ⟨hsubnormal, hquasisimple⟩
    exact ⟨le_top, Components.chain_of_mathlib_subnormal hsubnormal,
      Components.quasisimple_of_equiv equivalence hquasisimple⟩

theorem restrict_nested {G : Type*} [Group G]
    (component smaller larger : Subgroup G) (hcomponentSmaller : component ≤ smaller)
    (hsmallerLarger : smaller ≤ larger)
    (hcomponent : IsComponentOf (component.subgroupOf larger) ⊤) :
    IsComponentOf (component.subgroupOf smaller) ⊤ := by
  obtain ⟨hsubnormal, hquasisimple⟩ :=
    (subgroupOf_iff component larger (hcomponentSmaller.trans hsmallerLarger)).mp hcomponent
  apply (subgroupOf_iff component smaller hcomponentSmaller).mpr
  refine ⟨?_, hquasisimple⟩
  have hchain := hsubnormal.comap (Subgroup.inclusion hsmallerLarger)
  rwa [Subgroup.comap_inclusion_subgroupOf] at hchain

theorem map_nested {G H : Type*} [Group G] [Group H] (equivalence : G ≃* H)
    (component overgroup : Subgroup G)
    (hcomponent : IsComponentOf (component.subgroupOf overgroup) ⊤) :
    IsComponentOf ((component.map equivalence.toMonoidHom).subgroupOf
      (overgroup.map equivalence.toMonoidHom)) ⊤ := by
  let restriction := equivalence.subgroupMap overgroup
  have hmap : (component.subgroupOf overgroup).map restriction.toMonoidHom =
      (component.map equivalence.toMonoidHom).subgroupOf
        (overgroup.map equivalence.toMonoidHom) := by
    ext member
    rw [Subgroup.mem_map_equiv]
    change equivalence.symm member.val ∈ component ↔ member.val ∈ component.map equivalence.toMonoidHom
    exact Subgroup.mem_map_equiv.symm
  rw [← hmap]
  exact (LocalComponents.equiv_iff restriction (component.subgroupOf overgroup)).mpr hcomponent

theorem extend_nested {G : Type*} [Group G]
    (component smaller larger : Subgroup G) (hcomponentSmaller : component ≤ smaller)
    (hsmallerLarger : smaller ≤ larger) (hsmaller : (smaller.subgroupOf larger).IsSubnormal)
    (hcomponent : IsComponentOf (component.subgroupOf smaller) ⊤) :
    IsComponentOf (component.subgroupOf larger) ⊤ := by
  obtain ⟨hsubnormal, hquasisimple⟩ :=
    (subgroupOf_iff component smaller hcomponentSmaller).mp hcomponent
  apply (subgroupOf_iff component larger (hcomponentSmaller.trans hsmallerLarger)).mpr
  refine ⟨?_, hquasisimple⟩
  let equivalence := (Subgroup.subgroupOfEquivOfLe hsmallerLarger).symm
  have hmap : (component.subgroupOf smaller).map equivalence.toMonoidHom =
      (component.subgroupOf larger).subgroupOf (smaller.subgroupOf larger) := by
    ext element
    constructor
    · rintro ⟨lift, hlift, rfl⟩
      exact hlift
    · intro hmem
      exact ⟨⟨element.val.val, element.property⟩, hmem, rfl⟩
  have hchain := hsubnormal.map (f := equivalence.toMonoidHom) equivalence.surjective
  rw [hmap] at hchain
  exact hchain.trans (by intro element hmem; exact hcomponentSmaller hmem) hsmaller

theorem nested_component {G : Type*} [Group G]
    (component smaller larger : Subgroup G) (hsmallerLarger : smaller ≤ larger)
    (hcomponent : IsComponentOf (component.subgroupOf smaller) ⊤) :
    IsComponentOf ((component.subgroupOf larger).subgroupOf (smaller.subgroupOf larger)) ⊤ := by
  let equivalence := (Subgroup.subgroupOfEquivOfLe hsmallerLarger).symm
  have hmap : (component.subgroupOf smaller).map equivalence.toMonoidHom =
      (component.subgroupOf larger).subgroupOf (smaller.subgroupOf larger) := by
    ext member
    constructor
    · rintro ⟨lift, hlift, rfl⟩
      exact hlift
    · intro hmem
      exact ⟨⟨member.val.val, member.property⟩, hmem, rfl⟩
  rw [← hmap]
  exact (LocalComponents.equiv_iff equivalence (component.subgroupOf smaller)).mpr hcomponent

theorem centralizer_restrict {G : Type*} [Group G]
    (component overgroup : Subgroup G) (element : G) (helement : element ∈ overgroup)
    (hcentralizer : Subgroup.centralizer {element} ≤ overgroup)
    (hcomponent : IsComponentOf (component.subgroupOf (Subgroup.centralizer {element})) ⊤) :
    IsComponentOf ((component.subgroupOf overgroup).subgroupOf
      (Subgroup.centralizer {(⟨element, helement⟩ : overgroup)})) ⊤ := by
  let equivalence : (Subgroup.centralizer {element}) ≃*
      (Subgroup.centralizer {(⟨element, helement⟩ : overgroup)}) :=
    { toFun := fun member => ⟨⟨member.val, hcentralizer member.property⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp member.property))⟩
      invFun := fun member => ⟨member.val.val,
        Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp member.property))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hmap : (component.subgroupOf (Subgroup.centralizer {element})).map equivalence.toMonoidHom =
      (component.subgroupOf overgroup).subgroupOf
        (Subgroup.centralizer {(⟨element, helement⟩ : overgroup)}) := by
    ext member
    rw [Subgroup.mem_map_equiv]
    rfl
  rw [← hmap]
  exact (LocalComponents.equiv_iff equivalence _).mpr hcomponent

theorem commute_local_distinct {G : Type*} [Group G] [Finite G]
    (first second overgroup : Subgroup G)
    (hfirstLe : first ≤ overgroup) (hsecondLe : second ≤ overgroup)
    (hfirst : IsComponentOf (first.subgroupOf overgroup) ⊤)
    (hsecond : IsComponentOf (second.subgroupOf overgroup) ⊤) (hne : first ≠ second) :
    ⁅first, second⁆ = ⊥ := by
  have hlocalNe : first.subgroupOf overgroup ≠ second.subgroupOf overgroup := by
    intro heq
    have hmap := congrArg (Subgroup.map overgroup.subtype) heq
    rw [Subgroup.map_subgroupOf_eq_of_le hfirstLe,
      Subgroup.map_subgroupOf_eq_of_le hsecondLe] at hmap
    exact hne hmap
  have hcommutes := LocalComponents.commute_of_ne _ _ hfirst hsecond hlocalNe
  have hmap := congrArg (Subgroup.map overgroup.subtype) hcommutes
  simpa only [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hfirstLe,
    Subgroup.map_subgroupOf_eq_of_le hsecondLe, Subgroup.map_bot] using hmap

theorem common_centralizer_transport {G : Type*} [Group G]
    (component overgroup : Subgroup G) (element : G) (helement : element ∈ overgroup)
    (hcomponent : IsComponentOf (component.subgroupOf (overgroup ⊓ Subgroup.centralizer {element})) ⊤) :
    IsComponentOf ((component.subgroupOf overgroup).subgroupOf
      (Subgroup.centralizer {(⟨element, helement⟩ : overgroup)})) ⊤ := by
  let equivalence : ↥(overgroup ⊓ Subgroup.centralizer {element}) ≃*
      (Subgroup.centralizer {(⟨element, helement⟩ : overgroup)}) :=
    { toFun := fun member => ⟨⟨member.val, member.property.1⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp member.property.2))⟩
      invFun := fun member => ⟨member.val.val, member.val.property,
        Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp member.property))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hmap : (component.subgroupOf (overgroup ⊓ Subgroup.centralizer {element})).map
      equivalence.toMonoidHom = (component.subgroupOf overgroup).subgroupOf
        (Subgroup.centralizer {(⟨element, helement⟩ : overgroup)}) := by
    ext member
    rw [Subgroup.mem_map_equiv]
    rfl
  rw [← hmap]
  exact (LocalComponents.equiv_iff equivalence _).mpr hcomponent

end CFSG.ComponentClassification.OrdinaryComponentTransport
