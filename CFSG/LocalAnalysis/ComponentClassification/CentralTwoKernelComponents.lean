module

public import Mathlib
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.Open.Defs
public import CFSG.Open.OrderForm
public import CFSG.LocalAnalysis.ComponentClassification.Components
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents
public import CFSG.LocalAnalysis.ComponentClassification.Layer
public import CFSG.LocalAnalysis.ComponentClassification.TwoComponents
public import CFSG.LocalAnalysis.ComponentClassification.TwoResidual
public import CFSG.LocalAnalysis.ComponentClassification.TwoComponentConvention
public import CFSG.LocalAnalysis.ComponentClassification.OddKernel
public import CFSG.LocalAnalysis.ComponentClassification.OddKernelTwoComponents
public import CFSG.LocalAnalysis.ComponentClassification.CentralExtensions
public import CFSG.LocalAnalysis.ComponentClassification.CentralTwoKernel

public section

open CFSG.Open

namespace CFSG.ComponentClassification.CentralTwoKernelComponents

theorem image {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hcentralKernel : quotient.ker ≤ Subgroup.center G) (htwoKernel : IsPGroup 2 quotient.ker)
    (component : Subgroup G) (hcomponent : TwoComponents.IsTwoComponent component) :
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
  have hcentralRestriction : restriction.ker ≤ Subgroup.center component := by
    rw [hkernel]
    exact CentralTwoKernel.restriction_kernel_central quotient hcentralKernel component
  have htwoRestriction : IsPGroup 2 restriction.ker := by
    rw [hkernel]
    exact CentralTwoKernel.restriction_kernel_two quotient htwoKernel component
  let hcoreMap := CentralTwoKernel.coreQuotientMap restriction hrestriction
  have hquasisimple : IsQuasisimple (image ⧸ componentClassificationOddCore image) :=
    CentralTwoKernel.quasisimple_of_surjective (TwoComponents.quasisimple_quotient hcomponent)
      hcoreMap (CentralTwoKernel.coreQuotientMap_surjective restriction hrestriction)
      (CentralTwoKernel.coreQuotientMap_kernel_central restriction hrestriction
        hcentralRestriction htwoRestriction)
  have hgenerated : TwoResidual.subgroup image = ⊤ := by
    have hmap := TwoResidual.image_of_surjective restriction hrestriction
    rw [TwoComponentConvention.residual_eq_top_of_twoComponent hcomponent,
      Subgroup.map_top_of_surjective _ hrestriction] at hmap
    exact hmap.symm
  exact (TwoComponentConvention.twoComponent_iff _).mpr
    ⟨Components.chain_of_mathlib_subnormal
      ((Components.mathlib_subnormal_of_chain hcomponent.1
        Subgroup.IsSubnormal.top).map hsurjective), hgenerated, hquasisimple⟩

theorem quasisimple_iff {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (_hsurjective : Function.Surjective quotient)
    (hcentralKernel : quotient.ker ≤ Subgroup.center G) (component : Subgroup G)
    (hcomponent : TwoComponents.IsTwoComponent component) :
    IsQuasisimple (component.map quotient) ↔ IsQuasisimple component := by
  let image := component.map quotient
  let restriction : component →* image :=
    (quotient.domRestrict component).codRestrict image
      fun element => Subgroup.mem_map_of_mem quotient element.property
  have hrestriction : Function.Surjective restriction := by
    intro element
    obtain ⟨lift, hmem, hlift⟩ := Subgroup.mem_map.mp element.property
    exact ⟨⟨lift, hmem⟩, Subtype.ext hlift⟩
  have hcentralRestriction : restriction.ker ≤ Subgroup.center component := by
    intro element hmem
    have hkernel : quotient element.val = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hmem)
    apply Subgroup.mem_center_iff.mpr
    intro other
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hcentralKernel hkernel)) other.val)
  let : Group.IsPerfect component := ⟨TwoComponents.perfect hcomponent⟩
  exact ⟨fun hquasisimple => CentralExtensions.quasisimple_of_surjective hquasisimple restriction
      hrestriction hcentralRestriction,
    fun hquasisimple => CentralTwoKernel.quasisimple_of_surjective hquasisimple restriction
      hrestriction hcentralRestriction⟩

theorem exists_lift {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hcentralKernel : quotient.ker ≤ Subgroup.center G) (htwoKernel : IsPGroup 2 quotient.ker)
    (component : Subgroup H) (hcomponent : TwoComponents.IsTwoComponent component) :
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
  have hcentralRestriction : restriction.ker ≤ Subgroup.center preimage := by
    intro element hmem
    have hkernel : quotient element.val = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hmem)
    apply Subgroup.mem_center_iff.mpr
    intro other
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hcentralKernel hkernel)) other.val)
  let derived := commutator preimage
  let : Group.IsPerfect component := ⟨TwoComponents.perfect hcomponent⟩
  let : Group.IsPerfect derived :=
    CentralExtensions.derived_perfect restriction hrestriction hcentralRestriction
  let derivedRestriction := restriction.domRestrict derived
  have hderivedRestriction : Function.Surjective derivedRestriction := by
    intro element
    have hmem : element ∈ derived.map restriction := by
      rw [CentralExtensions.derived_map_eq_top restriction hrestriction]
      exact Subgroup.mem_top _
    obtain ⟨lift, hmem, hlift⟩ := Subgroup.mem_map.mp hmem
    exact ⟨⟨lift, hmem⟩, hlift⟩
  have hrestrictionKernel : restriction.ker = (quotient.domRestrict preimage).ker := by
    ext element
    change restriction element = 1 ↔ quotient element.val = 1
    exact ⟨fun hone => congrArg Subtype.val hone, fun hone => Subtype.ext hone⟩
  have htwoRestriction : IsPGroup 2 restriction.ker := by
    rw [hrestrictionKernel]
    exact CentralTwoKernel.restriction_kernel_two quotient htwoKernel preimage
  have hderivedCentral : derivedRestriction.ker ≤ Subgroup.center derived :=
    CentralTwoKernel.restriction_kernel_central restriction hcentralRestriction derived
  have hderivedTwo : IsPGroup 2 derivedRestriction.ker :=
    CentralTwoKernel.restriction_kernel_two restriction htwoRestriction derived
  have hderivedGenerated : TwoResidual.subgroup derived = ⊤ :=
    CentralTwoKernel.residual_eq_top_of_two_kernel derivedRestriction hderivedRestriction
      hderivedTwo (TwoComponentConvention.residual_eq_top_of_twoComponent hcomponent)
  have hderivedQuasisimple : IsQuasisimple (derived ⧸ componentClassificationOddCore derived) :=
    CentralExtensions.quasisimple_of_surjective (TwoComponents.quasisimple_quotient hcomponent)
      (CentralTwoKernel.coreQuotientMap derivedRestriction hderivedRestriction)
      (CentralTwoKernel.coreQuotientMap_surjective derivedRestriction hderivedRestriction)
      (CentralTwoKernel.coreQuotientMap_kernel_central derivedRestriction hderivedRestriction
        hderivedCentral hderivedTwo)
  have hderivedChain : derived.IsSubnormal :=
    Subgroup.IsSubnormal.step derived ⊤ le_top Subgroup.IsSubnormal.top inferInstance
  have hpreimageChain := (Components.mathlib_subnormal_of_chain hcomponent.1
    Subgroup.IsSubnormal.top).comap quotient
  let lift := derived.map preimage.subtype
  let equivalence : derived ≃* lift :=
    derived.equivMapOfInjective preimage.subtype preimage.subtype_injective
  have hliftChain : IsSubnormal lift ⊤ :=
    Components.chain_of_mathlib_subnormal (hderivedChain.trans' hpreimageChain)
  have hliftGenerated : TwoResidual.subgroup lift = ⊤ := by
    have hmap := TwoResidual.image_of_surjective equivalence.toMonoidHom equivalence.surjective
    rw [hderivedGenerated, Subgroup.map_top_of_surjective _ equivalence.surjective] at hmap
    exact hmap.symm
  have hliftQuasisimple : IsQuasisimple (lift ⧸ componentClassificationOddCore lift) :=
    Components.quasisimple_of_equiv
      (OddKernel.coreQuotientEquiv equivalence.toMonoidHom equivalence.surjective
        (by rw [(MonoidHom.ker_eq_bot_iff _).mpr equivalence.injective]; simp)).symm
      hderivedQuasisimple
  refine ⟨lift, (TwoComponentConvention.twoComponent_iff lift).mpr
    ⟨hliftChain, hliftGenerated, hliftQuasisimple⟩, ?_⟩
  ext element
  constructor
  · rintro ⟨member, ⟨liftMember, _, rfl⟩, rfl⟩
    exact liftMember.property
  · intro hmem
    obtain ⟨member, hvalue⟩ := hderivedRestriction ⟨element, hmem⟩
    exact ⟨member.val.val, ⟨member.val, member.property, rfl⟩, congrArg Subtype.val hvalue⟩

theorem derived_preimage_eq {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hcentralKernel : quotient.ker ≤ Subgroup.center G)
    (component : Subgroup G) (hcomponent : TwoComponents.IsTwoComponent component) :
    ⁅(component.map quotient).comap quotient, (component.map quotient).comap quotient⁆ =
      component := by
  rw [Subgroup.comap_map_eq,
    CentralExtensions.commutator_sup_central component quotient.ker hcentralKernel]
  let : Group.IsPerfect component := ⟨TwoComponents.perfect hcomponent⟩
  exact Subgroup.commutator_eq_self

theorem lift_unique {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hcentralKernel : quotient.ker ≤ Subgroup.center G)
    (first second : Subgroup G) (hfirst : TwoComponents.IsTwoComponent first)
    (hsecond : TwoComponents.IsTwoComponent second) (himages : first.map quotient = second.map quotient) :
    first = second := by
  have hfirstDerived := derived_preimage_eq quotient hcentralKernel first hfirst
  have hsecondDerived := derived_preimage_eq quotient hcentralKernel second hsecond
  rw [himages] at hfirstDerived
  exact hfirstDerived.symm.trans hsecondDerived

theorem bijOn {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hcentralKernel : quotient.ker ≤ Subgroup.center G) (htwoKernel : IsPGroup 2 quotient.ker) :
    Set.BijOn (Subgroup.map quotient) {component | TwoComponents.IsTwoComponent component}
      {component | TwoComponents.IsTwoComponent component} := by
  refine ⟨?_, ?_, ?_⟩
  · intro component hcomponent
    exact image quotient hsurjective hcentralKernel htwoKernel component hcomponent
  · intro first hfirst second hsecond himages
    exact lift_unique quotient hcentralKernel first second hfirst hsecond himages
  · intro component hcomponent
    obtain ⟨lift, hlift, hmap⟩ :=
      exists_lift quotient hsurjective hcentralKernel htwoKernel component hcomponent
    exact ⟨lift, hlift, hmap⟩

end CFSG.ComponentClassification.CentralTwoKernelComponents
