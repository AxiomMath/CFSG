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
public import CFSG.LocalAnalysis.ComponentClassification.TwoComponentConvention
public import CFSG.LocalAnalysis.ComponentClassification.OddKernel

public section

open CFSG.Open

namespace CFSG.ComponentClassification.OddKernelTwoComponents

theorem image {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hoddKernel : Odd (Nat.card quotient.ker)) (component : Subgroup G)
    (hcomponent : TwoComponents.IsTwoComponent component) :
    TwoComponents.IsTwoComponent (component.map quotient) := by
  let image := component.map quotient
  let restriction : component →* image :=
    (quotient.domRestrict component).codRestrict image
      fun element => Subgroup.mem_map_of_mem quotient element.property
  have hrestriction : Function.Surjective restriction := by
    intro element
    obtain ⟨lift, hmem, hlift⟩ := Subgroup.mem_map.mp element.property
    exact ⟨⟨lift, hmem⟩, Subtype.ext hlift⟩
  have hkernel : restriction.ker = (quotient.domRestrict component).ker := by
    ext element
    change restriction element = 1 ↔ quotient element.val = 1
    exact ⟨fun hone => congrArg Subtype.val hone, fun hone => Subtype.ext hone⟩
  have hoddRestriction : Odd (Nat.card restriction.ker) := by
    rw [hkernel]
    exact OddKernel.odd_card_restriction_kernel quotient hoddKernel component
  have hquasisimple : IsQuasisimple (image ⧸ componentClassificationOddCore image) :=
    Components.quasisimple_of_equiv
      (OddKernel.coreQuotientEquiv restriction hrestriction hoddRestriction).symm
      (TwoComponents.quasisimple_quotient hcomponent)
  have hgenerated : TwoResidual.subgroup image = ⊤ := by
    have hmap := TwoResidual.image_of_surjective restriction hrestriction
    rw [TwoComponentConvention.residual_eq_top_of_twoComponent hcomponent,
      Subgroup.map_top_of_surjective restriction hrestriction] at hmap
    exact hmap.symm
  apply (TwoComponentConvention.twoComponent_iff _).mpr
  exact ⟨Components.chain_of_mathlib_subnormal
    ((Components.mathlib_subnormal_of_chain hcomponent.1
      Subgroup.IsSubnormal.top).map hsurjective), hgenerated, hquasisimple⟩

theorem exists_lift {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hoddKernel : Odd (Nat.card quotient.ker)) (component : Subgroup H)
    (hcomponent : TwoComponents.IsTwoComponent component) :
    ∃ lift : Subgroup G, TwoComponents.IsTwoComponent lift ∧ lift.map quotient = component := by
  let preimage := component.comap quotient
  let restriction : preimage →* component :=
    (quotient.domRestrict preimage).codRestrict component fun element => element.property
  have hrestriction : Function.Surjective restriction := by
    intro element
    obtain ⟨lift, hlift⟩ := hsurjective element.val
    have hmem : lift ∈ preimage := by
      change quotient lift ∈ component
      rw [hlift]
      exact element.property
    exact ⟨⟨lift, hmem⟩, Subtype.ext hlift⟩
  have hkernel : restriction.ker = (quotient.domRestrict preimage).ker := by
    ext element
    change restriction element = 1 ↔ quotient element.val = 1
    exact ⟨fun hone => congrArg Subtype.val hone, fun hone => Subtype.ext hone⟩
  have hoddRestriction : Odd (Nat.card restriction.ker) := by
    rw [hkernel]
    exact OddKernel.odd_card_restriction_kernel quotient hoddKernel preimage
  have hquasisimple : IsQuasisimple (preimage ⧸ componentClassificationOddCore preimage) :=
    Components.quasisimple_of_equiv
      (OddKernel.coreQuotientEquiv restriction hrestriction hoddRestriction)
      (TwoComponents.quasisimple_quotient hcomponent)
  let residual := TwoResidual.subgroup preimage
  let : residual.Characteristic := TwoResidual.characteristic preimage
  have hresidualChain : IsSubnormal residual ⊤ :=
    Components.chain_of_mathlib_subnormal
      (Subgroup.IsSubnormal.step residual ⊤ le_top Subgroup.IsSubnormal.top inferInstance)
  let coreQuotient := QuotientGroup.mk' (componentClassificationOddCore preimage)
  have hresidualMap : residual.map coreQuotient = ⊤ := by
    rw [TwoResidual.image_of_surjective coreQuotient (QuotientGroup.mk'_surjective _)]
    exact QuasisimpleTwoGeneration.residual_eq_top_of_corefree hquasisimple
      (OddCore.quotient_corefree preimage)
  have hresidualQuasisimple : IsQuasisimple (residual ⧸ componentClassificationOddCore residual) := by
    let equivalence := Components.oddCore_image_equiv residual hresidualChain
    let imageEquivalence : (residual.map coreQuotient) ≃* (preimage ⧸ componentClassificationOddCore preimage) :=
      (MulEquiv.subgroupCongr hresidualMap).trans Subgroup.topEquiv
    exact Components.quasisimple_of_equiv (equivalence.trans imageEquivalence) hquasisimple
  have hresidualGenerated : TwoResidual.subgroup residual = ⊤ := by
    have hidempotent := TwoResidual.idempotent preimage
    apply top_unique
    intro element _
    have hmem : element.val ∈ (TwoResidual.subgroup residual).map residual.subtype := by
      rw [hidempotent]
      exact element.property
    obtain ⟨member, hmember, hvalue⟩ := Subgroup.mem_map.mp hmem
    exact (Subtype.ext hvalue : member = element) ▸ hmember
  let lift := residual.map preimage.subtype
  have hpreimageChain := (Components.mathlib_subnormal_of_chain hcomponent.1
    Subgroup.IsSubnormal.top).comap quotient
  have hliftChain : IsSubnormal lift ⊤ := Components.chain_of_mathlib_subnormal
    ((Components.mathlib_subnormal_of_chain hresidualChain Subgroup.IsSubnormal.top).trans'
      hpreimageChain)
  let equivalence : residual ≃* lift :=
    residual.equivMapOfInjective preimage.subtype preimage.subtype_injective
  have hliftGenerated : TwoResidual.subgroup lift = ⊤ := by
    have hmap := TwoResidual.image_of_surjective equivalence.toMonoidHom equivalence.surjective
    rw [hresidualGenerated, Subgroup.map_top_of_surjective _ equivalence.surjective] at hmap
    exact hmap.symm
  have hliftQuasisimple : IsQuasisimple (lift ⧸ componentClassificationOddCore lift) :=
    Components.quasisimple_of_equiv
      (OddKernel.coreQuotientEquiv equivalence.toMonoidHom equivalence.surjective
        (by rw [(MonoidHom.ker_eq_bot_iff _).mpr equivalence.injective]; simp)).symm
      hresidualQuasisimple
  have hlift : TwoComponents.IsTwoComponent lift :=
    (TwoComponentConvention.twoComponent_iff lift).mpr
      ⟨hliftChain, hliftGenerated, hliftQuasisimple⟩
  have himage : residual.map restriction = ⊤ := by
    rw [TwoResidual.image_of_surjective restriction hrestriction]
    exact TwoComponentConvention.residual_eq_top_of_twoComponent hcomponent
  refine ⟨lift, hlift, ?_⟩
  ext element
  constructor
  · rintro ⟨member, ⟨liftMember, _, rfl⟩, rfl⟩
    exact liftMember.property
  · intro hmem
    have htarget : (⟨element, hmem⟩ : component) ∈ residual.map restriction := by
      rw [himage]
      exact Subgroup.mem_top _
    obtain ⟨member, hmember, hvalue⟩ := Subgroup.mem_map.mp htarget
    exact ⟨member.val, ⟨member, hmember, rfl⟩, congrArg Subtype.val hvalue⟩

theorem lift_subgroupOf_eq_residual {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hoddKernel : Odd (Nat.card quotient.ker)) (component : Subgroup G)
    (hcomponent : TwoComponents.IsTwoComponent component) :
    component.subgroupOf ((component.map quotient).comap quotient) =
      TwoResidual.subgroup ((component.map quotient).comap quotient) := by
  let image := component.map quotient
  let preimage := image.comap quotient
  let restriction : preimage →* image :=
    (quotient.domRestrict preimage).codRestrict image fun element => element.property
  have hrestriction : Function.Surjective restriction := by
    intro element
    obtain ⟨lift, hlift⟩ := hsurjective element.val
    have hmem : lift ∈ preimage := by
      change quotient lift ∈ image
      rw [hlift]
      exact element.property
    exact ⟨⟨lift, hmem⟩, Subtype.ext hlift⟩
  have hkernel : restriction.ker = (quotient.domRestrict preimage).ker := by
    ext element
    change restriction element = 1 ↔ quotient element.val = 1
    exact ⟨fun hone => congrArg Subtype.val hone, fun hone => Subtype.ext hone⟩
  have hoddRestriction : Odd (Nat.card restriction.ker) := by
    rw [hkernel]
    exact OddKernel.odd_card_restriction_kernel quotient hoddKernel preimage
  have hle : component ≤ preimage := Subgroup.le_comap_map quotient component
  let equivalence := Subgroup.subgroupOfEquivOfLe hle
  have hgenerated : TwoResidual.subgroup (component.subgroupOf preimage) = ⊤ := by
    have hmap := TwoResidual.image_of_surjective equivalence.symm.toMonoidHom
      equivalence.symm.surjective
    rw [TwoComponentConvention.residual_eq_top_of_twoComponent hcomponent,
      Subgroup.map_top_of_surjective _ equivalence.symm.surjective] at hmap
    exact hmap.symm
  have hlocalChain : IsSubnormal (component.subgroupOf preimage) ⊤ :=
    Components.chain_of_mathlib_subnormal
      ((Components.mathlib_subnormal_of_chain hcomponent.1
        Subgroup.IsSubnormal.top).subgroupOf)
  have hcovering : Function.Surjective
      (restriction.domRestrict (component.subgroupOf preimage)) := by
    intro element
    obtain ⟨lift, hmem, hlift⟩ := Subgroup.mem_map.mp element.property
    exact ⟨⟨⟨lift, hle hmem⟩, hmem⟩, Subtype.ext hlift⟩
  exact TwoResidual.eq_of_subnormal_covering restriction hrestriction hoddRestriction
    (component.subgroupOf preimage) hlocalChain hgenerated hcovering

theorem lift_unique {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hoddKernel : Odd (Nat.card quotient.ker)) (first second : Subgroup G)
    (hfirst : TwoComponents.IsTwoComponent first) (hsecond : TwoComponents.IsTwoComponent second)
    (himages : first.map quotient = second.map quotient) : first = second := by
  have hfirstResidual := lift_subgroupOf_eq_residual quotient hsurjective hoddKernel first hfirst
  have hsecondResidual := lift_subgroupOf_eq_residual quotient hsurjective hoddKernel second hsecond
  rw [himages] at hfirstResidual
  have hlocalEq : first.subgroupOf ((second.map quotient).comap quotient) =
      second.subgroupOf ((second.map quotient).comap quotient) :=
    hfirstResidual.trans hsecondResidual.symm
  have hfirstLe : first ≤ (second.map quotient).comap quotient := by
    rw [← himages]
    exact Subgroup.le_comap_map quotient first
  have hmap := congrArg (Subgroup.map ((second.map quotient).comap quotient).subtype) hlocalEq
  simpa only [Subgroup.map_subgroupOf_eq_of_le hfirstLe,
    Subgroup.map_subgroupOf_eq_of_le (Subgroup.le_comap_map quotient second)] using hmap

theorem bijOn {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hoddKernel : Odd (Nat.card quotient.ker)) :
    Set.BijOn (Subgroup.map quotient) {component | TwoComponents.IsTwoComponent component}
      {component | TwoComponents.IsTwoComponent component} := by
  refine ⟨?_, ?_, ?_⟩
  · intro component hcomponent
    exact image quotient hsurjective hoddKernel component hcomponent
  · intro first hfirst second hsecond himages
    exact lift_unique quotient hsurjective hoddKernel first second hfirst hsecond himages
  · intro component hcomponent
    obtain ⟨lift, hlift, hmap⟩ := exists_lift quotient hsurjective hoddKernel component hcomponent
    exact ⟨lift, hlift, hmap⟩

end CFSG.ComponentClassification.OddKernelTwoComponents
