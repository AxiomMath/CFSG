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
public import CFSG.LocalAnalysis.ComponentClassification.QuasisimpleTwoGeneration

public section

open CFSG.Open

namespace CFSG.ComponentClassification.TwoComponentConvention

theorem residual_eq_top_of_twoComponent {G : Type*} [Group G] [Finite G]
    {component : Subgroup G} (hcomponent : TwoComponents.IsTwoComponent component) :
    TwoResidual.subgroup component = ⊤ := by
  let core := componentClassificationOddCore component
  let quotient := QuotientGroup.mk' core
  have hquotientGenerated : TwoResidual.subgroup (component ⧸ core) = ⊤ :=
    QuasisimpleTwoGeneration.residual_eq_top_of_corefree
      (TwoComponents.quasisimple_quotient hcomponent) (OddCore.quotient_corefree component)
  have hresidualMap : (TwoResidual.subgroup component).map quotient = ⊤ := by
    rw [TwoResidual.image_of_surjective quotient (QuotientGroup.mk'_surjective core)]
    exact hquotientGenerated
  let residual := TwoResidual.subgroup component
  let ambientResidual := residual.map component.subtype
  let : residual.Characteristic := TwoResidual.characteristic component
  have hresidualChain : residual.IsSubnormal :=
    Subgroup.IsSubnormal.step residual ⊤ le_top Subgroup.IsSubnormal.top inferInstance
  have hambientChain : IsSubnormal ambientResidual ⊤ :=
    Components.chain_of_mathlib_subnormal
      (hresidualChain.trans' (Components.mathlib_subnormal_of_chain hcomponent.1
        Subgroup.IsSubnormal.top))
  have hambientMap : ambientResidual.map
      (QuotientGroup.mk' (componentClassificationOddCore G)) =
      component.map (QuotientGroup.mk' (componentClassificationOddCore G)) := by
    apply le_antisymm (Subgroup.map_mono (Subgroup.map_subtype_le residual))
    intro element hmem
    obtain ⟨member, hmember, rfl⟩ := Subgroup.mem_map.mp hmem
    have htarget : quotient (⟨member, hmember⟩ : component) ∈ residual.map quotient := by
      rw [hresidualMap]
      exact Subgroup.mem_top _
    obtain ⟨lift, hlift, hvalue⟩ := Subgroup.mem_map.mp htarget
    have hkernel : lift⁻¹ * (⟨member, hmember⟩ : component) ∈ core := by
      apply (QuotientGroup.eq_one_iff _).mp
      change quotient (lift⁻¹ * (⟨member, hmember⟩ : component)) = 1
      rw [map_mul, map_inv, hvalue, inv_mul_cancel]
    have hambientKernel : lift.val⁻¹ * member ∈ componentClassificationOddCore G := by
      change lift⁻¹ * (⟨member, hmember⟩ : component) ∈
        (componentClassificationOddCore G).subgroupOf component
      rw [← OddCore.subnormal_intersection component hcomponent.1]
      exact hkernel
    have hambientValue : (QuotientGroup.mk' (componentClassificationOddCore G)) lift.val =
        (QuotientGroup.mk' (componentClassificationOddCore G)) member := by
      have hone := (QuotientGroup.eq_one_iff _).mpr hambientKernel
      change (QuotientGroup.mk' (componentClassificationOddCore G)) (lift.val⁻¹ * member) = 1 at hone
      rw [map_mul, map_inv] at hone
      exact inv_mul_eq_one.mp hone
    exact ⟨lift.val, ⟨lift, hlift, rfl⟩, hambientValue⟩
  have hambientEq := hcomponent.2.2 ambientResidual (Subgroup.map_subtype_le residual)
    hambientChain hambientMap
  have hlocalEq : residual = ⊤ := by
    apply top_unique
    intro element _
    have hmem : element.val ∈ ambientResidual := by
      rw [hambientEq]
      exact element.property
    obtain ⟨lift, hlift, hvalue⟩ := Subgroup.mem_map.mp hmem
    have heq : lift = element := Subtype.ext hvalue
    exact heq ▸ hlift
  exact hlocalEq

theorem twoComponent_iff {G : Type*} [Group G] [Finite G] (component : Subgroup G) :
    TwoComponents.IsTwoComponent component ↔
      IsSubnormal component ⊤ ∧ TwoResidual.subgroup component = ⊤ ∧
        IsQuasisimple (component ⧸ componentClassificationOddCore component) := by
  constructor
  · intro hcomponent
    exact ⟨hcomponent.1, residual_eq_top_of_twoComponent hcomponent,
      TwoComponents.quasisimple_quotient hcomponent⟩
  · rintro ⟨hsubnormal, hgenerated, hquasisimple⟩
    refine ⟨hsubnormal, (Components.quotient_component_iff component hsubnormal).mpr hquasisimple, ?_⟩
    intro smaller hle hsmallerChain hmap
    let quotient := (QuotientGroup.mk' (componentClassificationOddCore G)).domRestrict component
    let image := component.map (QuotientGroup.mk' (componentClassificationOddCore G))
    let restriction : component →* image := quotient.codRestrict image
      fun element => Subgroup.mem_map_of_mem _ element.property
    have hsurjective : Function.Surjective restriction := by
      intro element
      obtain ⟨member, hmember, hvalue⟩ := Subgroup.mem_map.mp element.property
      exact ⟨⟨member, hmember⟩, Subtype.ext hvalue⟩
    have hkernel : restriction.ker = componentClassificationOddCore component := by
      ext element
      change restriction element = 1 ↔ element ∈ componentClassificationOddCore component
      rw [← Components.oddCore_restriction_kernel component hsubnormal]
      exact ⟨fun hone => congrArg Subtype.val hone, fun hone => Subtype.ext hone⟩
    have hcovering : Function.Surjective (restriction.domRestrict (smaller.subgroupOf component)) := by
      intro element
      have hmem : element.val ∈ smaller.map
          (QuotientGroup.mk' (componentClassificationOddCore G)) := by
        rw [hmap]
        exact element.property
      obtain ⟨member, hmember, hvalue⟩ := Subgroup.mem_map.mp hmem
      exact ⟨⟨⟨member, hle hmember⟩, hmember⟩, Subtype.ext hvalue⟩
    have hoddIndex := TwoResidual.odd_index_of_covering restriction hsurjective
      (by rw [hkernel]; exact OddCore.odd_card component) (smaller.subgroupOf component) hcovering
    have hlocalSubnormal : IsSubnormal (smaller.subgroupOf component) ⊤ :=
      Components.chain_of_mathlib_subnormal
        ((Components.mathlib_subnormal_of_chain hsmallerChain Subgroup.IsSubnormal.top).subgroupOf)
    have hcontains := TwoResidual.subnormal_contains_of_odd_index
      (smaller.subgroupOf component) hlocalSubnormal hoddIndex
    rw [hgenerated] at hcontains
    exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp (top_unique hcontains))

end CFSG.ComponentClassification.TwoComponentConvention
