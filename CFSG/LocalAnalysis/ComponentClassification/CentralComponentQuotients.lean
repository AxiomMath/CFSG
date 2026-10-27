module

public import CFSG.LocalAnalysis.ComponentClassification.CentralExtensions

public section

open CFSG.Open

namespace CFSG.ComponentClassification.CentralComponentQuotients

theorem lift {G H : Type*} [Group G] [Group H] (quotient : G →* H)
    (hsurjective : Function.Surjective quotient)
    (hcentralKernel : quotient.ker ≤ Subgroup.center G) (component : Subgroup H)
    (hcomponent : IsComponentOf component ⊤) :
    ∃ lift : Subgroup G, IsComponentOf lift ⊤ ∧ lift.map quotient = component := by
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
  have hkernel : restriction.ker ≤ Subgroup.center preimage := by
    intro element hmem
    have hone : restriction element = 1 := MonoidHom.mem_ker.mp hmem
    have hcentral : element.val ∈ Subgroup.center G :=
      hcentralKernel (congrArg Subtype.val hone)
    apply Subgroup.mem_center_iff.mpr
    intro other
    exact Subtype.ext ((Subgroup.mem_center_iff.mp hcentral) other.val)
  let derived := commutator preimage
  have hquasisimple : IsQuasisimple derived :=
    CentralExtensions.derived_quasisimple hcomponent.2.2 restriction hrestriction hkernel
  have hderivedSubnormal : derived.IsSubnormal :=
    Subgroup.IsSubnormal.step derived ⊤ le_top Subgroup.IsSubnormal.top inferInstance
  have hpreimageSubnormal : IsSubnormal preimage ⊤ :=
    Components.chain_of_mathlib_subnormal
      ((Components.mathlib_subnormal_of_chain hcomponent.2.1
        Subgroup.IsSubnormal.top).comap quotient)
  let : Group.IsPerfect component := ⟨hcomponent.2.2.1⟩
  have hmap : derived.map restriction = ⊤ :=
    CentralExtensions.derived_map_eq_top restriction hrestriction
  refine ⟨derived.map preimage.subtype,
    LocalComponents.of_subnormal_subgroup preimage hpreimageSubnormal derived
      ⟨le_top, Components.chain_of_mathlib_subnormal hderivedSubnormal, hquasisimple⟩, ?_⟩
  ext element
  constructor
  · rintro ⟨lift, ⟨member, _, rfl⟩, rfl⟩
    exact member.property
  · intro hmem
    have htop : (⟨element, hmem⟩ : component) ∈ derived.map restriction := by
      rw [hmap]
      exact Subgroup.mem_top _
    obtain ⟨member, hmember, hvalue⟩ := Subgroup.mem_map.mp htop
    exact ⟨member.val, ⟨member, hmember, rfl⟩, congrArg Subtype.val hvalue⟩

theorem layer_map {G H : Type*} [Group G] [Group H] (quotient : G →* H)
    (hsurjective : Function.Surjective quotient)
    (hcentralKernel : quotient.ker ≤ Subgroup.center G) :
    (Layer.subgroup G).map quotient = Layer.subgroup H := by
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply sSup_le
    intro component hcomponent
    apply Subgroup.map_le_iff_le_comap.mp
    by_cases hkilled : component ≤ quotient.ker
    · rw [component.map_eq_bot_iff.mpr hkilled]
      exact bot_le
    · exact Layer.component_le (LocalComponents.image hcomponent quotient hsurjective hkilled)
  · apply sSup_le
    intro component hcomponent
    obtain ⟨preimage, hpreimage, hmap⟩ :=
      lift quotient hsurjective hcentralKernel component hcomponent
    rw [← hmap]
    exact Subgroup.map_mono (Layer.component_le hpreimage)

end CFSG.ComponentClassification.CentralComponentQuotients
