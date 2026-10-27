module

public import CFSG.LocalAnalysis.ComponentClassification.CentralTwoKernelComponents

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BadComponents

theorem perfect (G : Type*) [Group G] : Group.IsPerfect (TwoComponents.badSubgroup G) := by
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (Subgroup.commutator_le_self _) _
  apply sSup_le
  intro component hcomponent
  let : Group.IsPerfect component := ⟨TwoComponents.perfect hcomponent.1⟩
  rw [← Subgroup.commutator_eq_self (H := component)]
  have hle : component ≤ TwoComponents.badSubgroup G := le_sSup hcomponent
  exact Subgroup.commutator_mono hle hle

theorem centralKernel_image {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hcentralKernel : quotient.ker ≤ Subgroup.center G) (htwoKernel : IsPGroup 2 quotient.ker) :
    (TwoComponents.badSubgroup G).map quotient = TwoComponents.badSubgroup H := by
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply sSup_le
    intro component hbad
    apply Subgroup.map_le_iff_le_comap.mp
    apply le_sSup
    exact ⟨CentralTwoKernelComponents.image quotient hsurjective hcentralKernel htwoKernel
      component hbad.1, fun hquasisimple => hbad.2
        ((CentralTwoKernelComponents.quasisimple_iff quotient hsurjective hcentralKernel
          component hbad.1).mp hquasisimple)⟩
  · apply sSup_le
    intro component hbad
    obtain ⟨lift, hlift, hmap⟩ := CentralTwoKernelComponents.exists_lift quotient hsurjective
      hcentralKernel htwoKernel component hbad.1
    have hnotQuasisimple : ¬ IsQuasisimple lift := by
      intro hquasisimple
      apply hbad.2
      rw [← hmap]
      exact (CentralTwoKernelComponents.quasisimple_iff quotient hsurjective hcentralKernel
        lift hlift).mpr hquasisimple
    rw [← hmap]
    exact Subgroup.map_mono (le_sSup ⟨hlift, hnotQuasisimple⟩)

theorem equiv_invariant {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (equivalence : G ≃* H) :
    (TwoComponents.badSubgroup G).map equivalence.toMonoidHom = TwoComponents.badSubgroup H := by
  have hkernel : equivalence.toMonoidHom.ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff _).mpr equivalence.injective
  exact centralKernel_image equivalence.toMonoidHom equivalence.surjective
    (by rw [hkernel]; exact bot_le) (by rw [hkernel]; exact IsPGroup.of_bot)

theorem characteristic (G : Type*) [Group G] [Finite G] :
    (TwoComponents.badSubgroup G).Characteristic := by
  apply Subgroup.characteristic_iff_map_eq.mpr
  intro automorphism
  exact equiv_invariant automorphism

theorem perfect_containment_of_central_kernel {G H : Type*} [Group G] [Group H]
    (quotient : G →* H) (hcentralKernel : quotient.ker ≤ Subgroup.center G)
    (perfectSubgroup containingSubgroup : Subgroup G) [Group.IsPerfect perfectSubgroup]
    (himages : perfectSubgroup.map quotient ≤ containingSubgroup.map quotient) :
    perfectSubgroup ≤ containingSubgroup := by
  have hpreimage := Subgroup.map_le_iff_le_comap.mp himages
  rw [Subgroup.comap_map_eq] at hpreimage
  calc
    perfectSubgroup = ⁅perfectSubgroup, perfectSubgroup⁆ := Subgroup.commutator_eq_self.symm
    _ ≤ ⁅containingSubgroup ⊔ quotient.ker, containingSubgroup ⊔ quotient.ker⁆ :=
      Subgroup.commutator_mono hpreimage hpreimage
    _ = ⁅containingSubgroup, containingSubgroup⁆ :=
      CentralExtensions.commutator_sup_central containingSubgroup quotient.ker hcentralKernel
    _ ≤ containingSubgroup := Subgroup.commutator_le_self _

theorem ambient_description {G : Type*} [Group G] (overgroup : Subgroup G) :
    (TwoComponents.badSubgroup overgroup).map overgroup.subtype =
      sSup {component : Subgroup G | component ≤ overgroup ∧
        TwoComponents.IsTwoComponent (component.subgroupOf overgroup) ∧
          ¬ IsQuasisimple component} := by
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply sSup_le
    intro component hbad
    apply Subgroup.map_le_iff_le_comap.mp
    apply le_sSup
    have hrestriction : (component.map overgroup.subtype).subgroupOf overgroup = component :=
      Subgroup.comap_map_eq_self_of_injective overgroup.subtype_injective component
    refine ⟨Subgroup.map_subtype_le component, ?_, ?_⟩
    · rw [hrestriction]
      exact hbad.1
    · intro hquasisimple
      exact hbad.2 (Components.quasisimple_of_equiv
        (component.equivMapOfInjective overgroup.subtype overgroup.subtype_injective)
        hquasisimple)
  · apply sSup_le
    rintro component ⟨hle, hcomponent, hnotQuasisimple⟩
    rw [← Subgroup.map_subgroupOf_eq_of_le hle]
    apply Subgroup.map_mono
    apply le_sSup
    refine ⟨hcomponent, ?_⟩
    intro hquasisimple
    exact hnotQuasisimple (Components.quasisimple_of_equiv
      (Subgroup.subgroupOfEquivOfLe hle).symm hquasisimple)

theorem ambient_image_of_central_two_kernel {G H : Type*}
    [Group G] [Finite G] [Group H] [Finite H]
    (quotient : G →* H) (hcentralKernel : quotient.ker ≤ Subgroup.center G)
    (htwoKernel : IsPGroup 2 quotient.ker) (overgroup : Subgroup G) :
    ((TwoComponents.badSubgroup overgroup).map overgroup.subtype).map quotient =
      (TwoComponents.badSubgroup (overgroup.map quotient)).map
        (overgroup.map quotient).subtype := by
  let image := overgroup.map quotient
  let restriction : overgroup →* image :=
    (quotient.domRestrict overgroup).codRestrict image
      fun element => Subgroup.mem_map_of_mem quotient element.property
  have hsurjective : Function.Surjective restriction := by
    intro element
    obtain ⟨lift, hmem, hvalue⟩ := Subgroup.mem_map.mp element.property
    exact ⟨⟨lift, hmem⟩, Subtype.ext hvalue⟩
  have hkernel : restriction.ker = (quotient.domRestrict overgroup).ker := by
    ext element
    change restriction element = 1 ↔ quotient element.val = 1
    exact ⟨fun hone => congrArg Subtype.val hone, fun hone => Subtype.ext hone⟩
  have hkernelCentral : restriction.ker ≤ Subgroup.center overgroup := by
    rw [hkernel]
    exact CentralTwoKernel.restriction_kernel_central quotient hcentralKernel overgroup
  have hkernelTwo : IsPGroup 2 restriction.ker := by
    rw [hkernel]
    exact CentralTwoKernel.restriction_kernel_two quotient htwoKernel overgroup
  have hcomposite : quotient.comp overgroup.subtype = image.subtype.comp restriction := rfl
  rw [Subgroup.map_map, hcomposite, ← Subgroup.map_map,
    centralKernel_image restriction hsurjective hkernelCentral hkernelTwo]

end CFSG.ComponentClassification.BadComponents
