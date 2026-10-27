module

public import Mathlib
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.Open.Defs
public import CFSG.Open.OrderForm
public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.LocalAnalysis.ComponentClassification.Components
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents
public import CFSG.LocalAnalysis.ComponentClassification.Layer
public import CFSG.LocalAnalysis.ComponentClassification.TwoComponents
public import CFSG.LocalAnalysis.ComponentClassification.TwoResidual
public import CFSG.LocalAnalysis.ComponentClassification.TwoComponentConvention
public import CFSG.LocalAnalysis.ComponentClassification.OddKernelTwoComponents

public section

open CFSG.Open

namespace CFSG.ComponentClassification.TwoComponentTransport

theorem residual_eq_top_of_equiv {G H : Type*} [Group G] [Group H]
    (equivalence : G ≃* H) (hgenerated : TwoResidual.subgroup G = ⊤) :
    TwoResidual.subgroup H = ⊤ := by
  have hmap := TwoResidual.equiv_invariant equivalence
  rw [hgenerated, Subgroup.map_top_of_surjective equivalence.toMonoidHom
    equivalence.surjective] at hmap
  exact hmap.symm

theorem quasisimple_coreQuotient_of_equiv {G H : Type*} [Group G] [Group H]
    (equivalence : G ≃* H)
    (hquasisimple : IsQuasisimple (G ⧸ componentClassificationOddCore G)) :
    IsQuasisimple (H ⧸ componentClassificationOddCore H) := by
  exact Components.quasisimple_of_equiv
    (QuotientGroup.congr (componentClassificationOddCore G)
      (componentClassificationOddCore H) equivalence (OddCore.equiv_invariant equivalence)).symm
    hquasisimple

theorem of_overgroup {G : Type*} [Group G] [Finite G]
    {component overgroup : Subgroup G} (hcomponent : TwoComponents.IsTwoComponent component)
    (hle : component ≤ overgroup) :
    TwoComponents.IsTwoComponent (component.subgroupOf overgroup) := by
  apply (TwoComponentConvention.twoComponent_iff _).mpr
  refine ⟨Components.chain_of_mathlib_subnormal
    ((Components.mathlib_subnormal_of_chain hcomponent.1
      Subgroup.IsSubnormal.top).subgroupOf), ?_, ?_⟩
  · exact residual_eq_top_of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
      (TwoComponentConvention.residual_eq_top_of_twoComponent hcomponent)
  · exact quasisimple_coreQuotient_of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
      (TwoComponents.quasisimple_quotient hcomponent)

theorem of_subnormal_subgroup {G : Type*} [Group G] [Finite G]
    (subgroup : Subgroup G) (hsubnormal : IsSubnormal subgroup ⊤)
    (component : Subgroup subgroup) (hcomponent : TwoComponents.IsTwoComponent component) :
    TwoComponents.IsTwoComponent (component.map subgroup.subtype) := by
  apply (TwoComponentConvention.twoComponent_iff _).mpr
  refine ⟨Components.chain_of_mathlib_subnormal
    ((Components.mathlib_subnormal_of_chain hcomponent.1 Subgroup.IsSubnormal.top).trans'
      (Components.mathlib_subnormal_of_chain hsubnormal Subgroup.IsSubnormal.top)), ?_, ?_⟩
  · exact residual_eq_top_of_equiv
      (component.equivMapOfInjective subgroup.subtype subgroup.subtype_injective)
      (TwoComponentConvention.residual_eq_top_of_twoComponent hcomponent)
  · exact quasisimple_coreQuotient_of_equiv
      (component.equivMapOfInjective subgroup.subtype subgroup.subtype_injective)
      (TwoComponents.quasisimple_quotient hcomponent)

theorem equiv_iff {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (equivalence : G ≃* H) (component : Subgroup G) :
    TwoComponents.IsTwoComponent (component.map equivalence.toMonoidHom) ↔
      TwoComponents.IsTwoComponent component := by
  constructor
  · intro hcomponent
    apply (TwoComponentConvention.twoComponent_iff _).mpr
    have hmap : (component.map equivalence.toMonoidHom).map equivalence.symm.toMonoidHom =
        component := by
      ext element
      constructor
      · rintro ⟨image, ⟨lift, hmem, rfl⟩, rfl⟩
        change equivalence.symm (equivalence lift) ∈ component
        rw [equivalence.symm_apply_apply]
        exact hmem
      · intro hmem
        exact ⟨equivalence element, ⟨element, hmem, rfl⟩,
          equivalence.symm_apply_apply element⟩
    refine ⟨?_, ?_, ?_⟩
    · apply Components.chain_of_mathlib_subnormal
      have hchain := (Components.mathlib_subnormal_of_chain hcomponent.1
        Subgroup.IsSubnormal.top).map (f := equivalence.symm.toMonoidHom)
          equivalence.symm.surjective
      rwa [hmap] at hchain
    · exact residual_eq_top_of_equiv
        (component.equivMapOfInjective equivalence.toMonoidHom equivalence.injective).symm
        (TwoComponentConvention.residual_eq_top_of_twoComponent hcomponent)
    · exact quasisimple_coreQuotient_of_equiv
        (component.equivMapOfInjective equivalence.toMonoidHom equivalence.injective).symm
        (TwoComponents.quasisimple_quotient hcomponent)
  · intro hcomponent
    apply (TwoComponentConvention.twoComponent_iff _).mpr
    refine ⟨Components.chain_of_mathlib_subnormal
      ((Components.mathlib_subnormal_of_chain hcomponent.1
        Subgroup.IsSubnormal.top).map equivalence.surjective), ?_, ?_⟩
    · exact residual_eq_top_of_equiv
        (component.equivMapOfInjective equivalence.toMonoidHom equivalence.injective)
        (TwoComponentConvention.residual_eq_top_of_twoComponent hcomponent)
    · exact quasisimple_coreQuotient_of_equiv
        (component.equivMapOfInjective equivalence.toMonoidHom equivalence.injective)
        (TwoComponents.quasisimple_quotient hcomponent)

theorem subgroupOf_iff {G : Type*} [Group G] [Finite G]
    (component overgroup : Subgroup G) (hle : component ≤ overgroup) :
    TwoComponents.IsTwoComponent (component.subgroupOf overgroup) ↔
      (component.subgroupOf overgroup).IsSubnormal ∧
        TwoResidual.subgroup component = ⊤ ∧
          IsQuasisimple (component ⧸ componentClassificationOddCore component) := by
  let equivalence := Subgroup.subgroupOfEquivOfLe hle
  constructor
  · intro hcomponent
    exact ⟨Components.mathlib_subnormal_of_chain hcomponent.1 Subgroup.IsSubnormal.top,
      residual_eq_top_of_equiv equivalence
        (TwoComponentConvention.residual_eq_top_of_twoComponent hcomponent),
      quasisimple_coreQuotient_of_equiv equivalence
        (TwoComponents.quasisimple_quotient hcomponent)⟩
  · rintro ⟨hsubnormal, hgenerated, hquasisimple⟩
    exact (TwoComponentConvention.twoComponent_iff _).mpr
      ⟨Components.chain_of_mathlib_subnormal hsubnormal,
        residual_eq_top_of_equiv equivalence.symm hgenerated,
        quasisimple_coreQuotient_of_equiv equivalence.symm hquasisimple⟩

theorem restrict_nested {G : Type*} [Group G] [Finite G]
    (component smaller larger : Subgroup G) (hcomponentSmaller : component ≤ smaller)
    (hsmallerLarger : smaller ≤ larger)
    (hcomponent : TwoComponents.IsTwoComponent (component.subgroupOf larger)) :
    TwoComponents.IsTwoComponent (component.subgroupOf smaller) := by
  obtain ⟨hsubnormal, hgenerated, hquasisimple⟩ :=
    (subgroupOf_iff component larger (hcomponentSmaller.trans hsmallerLarger)).mp hcomponent
  apply (subgroupOf_iff component smaller hcomponentSmaller).mpr
  refine ⟨?_, hgenerated, hquasisimple⟩
  have hchain := hsubnormal.comap (Subgroup.inclusion hsmallerLarger)
  rwa [Subgroup.comap_inclusion_subgroupOf] at hchain

theorem extend_nested {G : Type*} [Group G] [Finite G]
    (component smaller larger : Subgroup G) (hcomponentSmaller : component ≤ smaller)
    (hsmallerLarger : smaller ≤ larger) (hsmaller : (smaller.subgroupOf larger).IsSubnormal)
    (hcomponent : TwoComponents.IsTwoComponent (component.subgroupOf smaller)) :
    TwoComponents.IsTwoComponent (component.subgroupOf larger) := by
  obtain ⟨hsubnormal, hgenerated, hquasisimple⟩ :=
    (subgroupOf_iff component smaller hcomponentSmaller).mp hcomponent
  apply (subgroupOf_iff component larger (hcomponentSmaller.trans hsmallerLarger)).mpr
  refine ⟨?_, hgenerated, hquasisimple⟩
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

end CFSG.ComponentClassification.TwoComponentTransport
