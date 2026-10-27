module

public import CFSG.LocalAnalysis.ComponentClassification.TwoComponentTransport

public section

open CFSG.Open

namespace CFSG.ComponentClassification.TwoComponentSubnormal

theorem ambient_residual_preimage {G H : Type*}
    [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hoddKernel : Odd (Nat.card quotient.ker)) (component : Subgroup G)
    (hcomponent : TwoComponents.IsTwoComponent component) :
    (TwoResidual.subgroup ((component.map quotient).comap quotient)).map
      ((component.map quotient).comap quotient).subtype = component := by
  rw [← OddKernelTwoComponents.lift_subgroupOf_eq_residual quotient hsurjective
    hoddKernel component hcomponent]
  exact Subgroup.map_subgroupOf_eq_of_le (Subgroup.le_comap_map quotient component)

theorem le_of_odd_kernel_map_le {G H : Type*}
    [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hoddKernel : Odd (Nat.card quotient.ker)) (component subnormalSubgroup : Subgroup G)
    (hcomponent : TwoComponents.IsTwoComponent component)
    (hsubnormal : IsSubnormal subnormalSubgroup ⊤)
    (himages : component.map quotient ≤ subnormalSubgroup.map quotient) :
    component ≤ subnormalSubgroup := by
  let image := subnormalSubgroup.map quotient
  let preimage := image.comap quotient
  let restriction : preimage →* image :=
    (quotient.domRestrict preimage).codRestrict image fun element => element.property
  have hsurjectiveRestriction : Function.Surjective restriction := by
    intro element
    obtain ⟨lift, hvalue⟩ := hsurjective element.val
    have hmem : lift ∈ preimage := by
      change quotient lift ∈ image
      rw [hvalue]
      exact element.property
    exact ⟨⟨lift, hmem⟩, Subtype.ext hvalue⟩
  have hkernel : restriction.ker = (quotient.domRestrict preimage).ker := by
    ext element
    change restriction element = 1 ↔ quotient element.val = 1
    exact ⟨fun hone => congrArg Subtype.val hone, fun hone => Subtype.ext hone⟩
  have hoddRestriction : Odd (Nat.card restriction.ker) := by
    rw [hkernel]
    exact OddKernel.odd_card_restriction_kernel quotient hoddKernel preimage
  have hsubnormalLe : subnormalSubgroup ≤ preimage := Subgroup.le_comap_map quotient _
  have hcovering : Function.Surjective
      (restriction.domRestrict (subnormalSubgroup.subgroupOf preimage)) := by
    intro element
    obtain ⟨lift, hmem, hvalue⟩ := Subgroup.mem_map.mp element.property
    exact ⟨⟨⟨lift, hsubnormalLe hmem⟩, hmem⟩, Subtype.ext hvalue⟩
  have hoddIndex := TwoResidual.odd_index_of_covering restriction hsurjectiveRestriction
    hoddRestriction (subnormalSubgroup.subgroupOf preimage) hcovering
  have hlocalChain : IsSubnormal (subnormalSubgroup.subgroupOf preimage) ⊤ :=
    Components.chain_of_mathlib_subnormal
      ((Components.mathlib_subnormal_of_chain hsubnormal Subgroup.IsSubnormal.top).subgroupOf)
  have hresidual := TwoResidual.subnormal_contains_of_odd_index
    (subnormalSubgroup.subgroupOf preimage) hlocalChain hoddIndex
  have hcomponentLe : component ≤ preimage := Subgroup.map_le_iff_le_comap.mp himages
  have hlocalComponent := TwoComponentTransport.of_overgroup hcomponent hcomponentLe
  have hgenerated := TwoComponentConvention.residual_eq_top_of_twoComponent hlocalComponent
  have hmap := TwoResidual.map_le (component.subgroupOf preimage).subtype
  rw [hgenerated] at hmap
  intro element hmem
  exact hresidual (hmap ⟨⟨⟨element, hcomponentLe hmem⟩, hmem⟩, Subgroup.mem_top _, rfl⟩)

theorem contains_or_normalizes_core {G : Type*} [Group G] [Finite G]
    (component subnormalSubgroup : Subgroup G)
    (hcomponent : TwoComponents.IsTwoComponent component)
    (hsubnormal : IsSubnormal subnormalSubgroup ⊤) :
    component ≤ subnormalSubgroup ∨
      (subnormalSubgroup ≤ Subgroup.normalizer (component : Set G) ∧
        ⁅component, subnormalSubgroup⁆ ≤
          (componentClassificationOddCore component).map component.subtype) := by
  let core := componentClassificationOddCore G
  let quotient := QuotientGroup.mk' core
  have hkernel : quotient.ker = core := QuotientGroup.ker_mk' core
  have hoddKernel : Odd (Nat.card quotient.ker) := by
    rw [hkernel]
    exact OddCore.odd_card G
  have hquotientSubnormal : IsSubnormal (subnormalSubgroup.map quotient) ⊤ := by
    have hchain := Components.chain_map quotient hsubnormal
    rwa [Subgroup.map_top_of_surjective quotient (QuotientGroup.mk'_surjective _)] at hchain
  rcases LocalComponents.subnormal_contains_or_commutes (component.map quotient)
      (subnormalSubgroup.map quotient) hcomponent.2.1 hquotientSubnormal with
    hcontained | hcommutes
  · exact Or.inl (le_of_odd_kernel_map_le quotient (QuotientGroup.mk'_surjective _)
      hoddKernel component subnormalSubgroup hcomponent hsubnormal hcontained)
  · right
    let preimage := (component.map quotient).comap quotient
    have hnormalizesImage : subnormalSubgroup.map quotient ≤
        Subgroup.normalizer (component.map quotient : Set (G ⧸ core)) := by
      rw [Subgroup.commutator_comm] at hcommutes
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes).trans
        (Subgroup.centralizer_le_normalizer _)
    have hnormalizesPreimage : subnormalSubgroup ≤ Subgroup.normalizer (preimage : Set G) :=
      (Subgroup.map_le_iff_le_comap.mp hnormalizesImage).trans
        (Subgroup.le_normalizer_comap quotient)
    have hcanonical := ambient_residual_preimage quotient (QuotientGroup.mk'_surjective _)
      hoddKernel component hcomponent
    have hnormalizesComponent : subnormalSubgroup ≤ Subgroup.normalizer (component : Set G) := by
      rw [← hcanonical]
      exact hnormalizesPreimage.trans (TwoResidual.normalizer_le_normalizer preimage)
    refine ⟨hnormalizesComponent, ?_⟩
    have hcoreCommutator : ⁅component, subnormalSubgroup⁆ ≤ core := by
      have hmap : (⁅component, subnormalSubgroup⁆).map quotient = ⊥ := by
        rw [Subgroup.map_commutator]
        exact hcommutes
      have hle := (Subgroup.map_eq_bot_iff _).mp hmap
      rwa [hkernel] at hle
    have hcomponentCommutator : ⁅component, subnormalSubgroup⁆ ≤ component :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp hnormalizesComponent
    rw [OddCore.subnormal_intersection component hcomponent.1,
      Subgroup.subgroupOf_map_subtype]
    exact le_inf hcoreCommutator hcomponentCommutator

theorem eq_of_le {G : Type*} [Group G] [Finite G]
    (first second : Subgroup G) (hfirst : TwoComponents.IsTwoComponent first)
    (hsecond : TwoComponents.IsTwoComponent second) (hle : first ≤ second) : first = second := by
  let quotient := QuotientGroup.mk' (componentClassificationOddCore G)
  have himages : first.map quotient = second.map quotient :=
    LocalComponents.eq_of_le _ _ hfirst.2.1 hsecond.2.1 (Subgroup.map_mono hle)
  apply OddKernelTwoComponents.lift_unique quotient (QuotientGroup.mk'_surjective _) _
    first second hfirst hsecond himages
  rw [QuotientGroup.ker_mk']
  exact OddCore.odd_card G

end CFSG.ComponentClassification.TwoComponentSubnormal
