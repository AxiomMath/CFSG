module

public import Mathlib
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.Open.Defs
public import CFSG.Open.OrderForm
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.Assembly.Subnormal

public section

open CFSG.Open

namespace CFSG.ComponentClassification.Components

theorem mathlib_subnormal_of_chain {G : Type*} [Group G] {lower upper : Subgroup G}
    (hchain : IsSubnormal lower upper) (hupper : upper.IsSubnormal) : lower.IsSubnormal :=
  hchain.mathlib hupper

theorem chain_of_mathlib_subnormal {G : Type*} [Group G] {subgroup : Subgroup G}
    (hsubnormal : subgroup.IsSubnormal) : IsSubnormal subgroup ⊤ :=
  IsSubnormal.of_mathlib hsubnormal

theorem chain_map {G H : Type*} [Group G] [Group H] (homomorphism : G →* H)
    {lower upper : Subgroup G} (hchain : IsSubnormal lower upper) :
    IsSubnormal (lower.map homomorphism) (upper.map homomorphism) :=
  hchain.map homomorphism

theorem perfect_subnormal_lift {G H : Type*} [Group G] [Finite G] [Group H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (component : Subgroup H) (hsubnormal : component.IsSubnormal)
    [Group.IsPerfect component] :
    ∃ lift : Subgroup G, IsSubnormal lift ⊤ ∧ lift.map quotient = component ∧
      commutator lift = ⊤ ∧
      ∀ smaller : Subgroup G, smaller ≤ lift → IsSubnormal smaller ⊤ →
        smaller.map quotient = component → smaller = lift := by
  have hpreimage : (component.comap quotient).IsSubnormal ∧
      (component.comap quotient).map quotient = component :=
    ⟨hsubnormal.comap quotient,
      Subgroup.map_comap_eq_self_of_surjective hsurjective component⟩
  obtain ⟨lift, _, hminimal⟩ := Finite.exists_le_minimal
    (p := fun lift : Subgroup G => lift.IsSubnormal ∧ lift.map quotient = component)
    hpreimage
  have hproperties := hminimal.prop
  have hderivedNormal : (⁅lift, lift⁆.subgroupOf lift).Normal := by
    have hsup : lift ⊔ lift = lift := le_antisymm (sup_le le_rfl le_rfl) le_sup_left
    have hnormal :=
      (inferInstance : (⁅lift, lift⁆.subgroupOf (lift ⊔ lift)).Normal)
    rw [hsup] at hnormal
    exact hnormal
  have hderivedSubnormal : ⁅lift, lift⁆.IsSubnormal :=
    Subgroup.IsSubnormal.step ⁅lift, lift⁆ lift
      (by simpa only [sup_idem] using Subgroup.commutator_le_sup lift lift)
      hproperties.1 hderivedNormal
  have hderivedMap : ⁅lift, lift⁆.map quotient = component := by
    rw [Subgroup.map_commutator, hproperties.2]
    exact Subgroup.commutator_eq_self
  have hperfect : Group.IsPerfect lift := by
    apply Subgroup.isPerfect_iff.mpr
    exact ((minimal_iff.mp hminimal).2 ⟨hderivedSubnormal, hderivedMap⟩
      (by simpa only [sup_idem] using Subgroup.commutator_le_sup lift lift)).symm
  refine ⟨lift, chain_of_mathlib_subnormal hproperties.1, hproperties.2,
    hperfect.commutator_eq_top, ?_⟩
  intro smaller hle hsubnormal hmap
  exact ((minimal_iff.mp hminimal).2
    ⟨mathlib_subnormal_of_chain hsubnormal Subgroup.IsSubnormal.top, hmap⟩ hle).symm

theorem oddCore_restriction_kernel {G : Type*} [Group G] [Finite G]
    (subgroup : Subgroup G) (hsubnormal : IsSubnormal subgroup ⊤) :
    ((QuotientGroup.mk' (componentClassificationOddCore G)).domRestrict subgroup).ker =
      componentClassificationOddCore subgroup := by
  rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
  exact (OddCore.subnormal_intersection subgroup hsubnormal).symm

noncomputable def oddCore_image_equiv {G : Type*} [Group G] [Finite G]
    (subgroup : Subgroup G) (hsubnormal : IsSubnormal subgroup ⊤) :
    (subgroup ⧸ componentClassificationOddCore subgroup) ≃*
      subgroup.map (QuotientGroup.mk' (componentClassificationOddCore G)) := by
  let quotient := QuotientGroup.mk' (componentClassificationOddCore G)
  let image := subgroup.map quotient
  let restriction : subgroup →* image :=
    (quotient.domRestrict subgroup).codRestrict image
      fun element => Subgroup.mem_map_of_mem quotient element.property
  have hsurjective : Function.Surjective restriction := by
    intro element
    obtain ⟨lift, hmem, hlift⟩ := Subgroup.mem_map.mp element.property
    exact ⟨⟨lift, hmem⟩, Subtype.ext hlift⟩
  have hkernel : restriction.ker = componentClassificationOddCore subgroup := by
    ext element
    change restriction element = 1 ↔ element ∈ componentClassificationOddCore subgroup
    rw [← oddCore_restriction_kernel subgroup hsubnormal]
    change restriction element = 1 ↔ quotient element.val = 1
    exact ⟨fun hone => congrArg Subtype.val hone, fun hone => Subtype.ext hone⟩
  exact QuotientGroup.liftEquiv (componentClassificationOddCore subgroup)
    hsurjective hkernel.symm

theorem quasisimple_of_equiv {G H : Type*} [Group G] [Group H]
    (equivalence : G ≃* H) (hquasisimple : IsQuasisimple H) : IsQuasisimple G :=
  hquasisimple.of_mulEquiv equivalence

theorem quotient_component_iff {G : Type*} [Group G] [Finite G]
    (subgroup : Subgroup G) (hsubnormal : IsSubnormal subgroup ⊤) :
    IsComponentOf (subgroup.map (QuotientGroup.mk' (componentClassificationOddCore G))) ⊤ ↔
      IsQuasisimple (subgroup ⧸ componentClassificationOddCore subgroup) := by
  let quotient := QuotientGroup.mk' (componentClassificationOddCore G)
  let equivalence := oddCore_image_equiv subgroup hsubnormal
  constructor
  · intro hcomponent
    exact quasisimple_of_equiv equivalence hcomponent.2.2
  · intro hquasisimple
    refine ⟨le_top, ?_, quasisimple_of_equiv equivalence.symm hquasisimple⟩
    apply chain_of_mathlib_subnormal
    exact (mathlib_subnormal_of_chain hsubnormal Subgroup.IsSubnormal.top).map
      (QuotientGroup.mk'_surjective (componentClassificationOddCore G))

theorem perfect_lift_of_component {G : Type*} [Group G] [Finite G]
    (component : Subgroup (G ⧸ componentClassificationOddCore G))
    (hcomponent : IsComponentOf component ⊤) :
    ∃ lift : Subgroup G, IsSubnormal lift ⊤ ∧
      lift.map (QuotientGroup.mk' (componentClassificationOddCore G)) = component ∧
      commutator lift = ⊤ ∧ IsQuasisimple (lift ⧸ componentClassificationOddCore lift) ∧
      ∀ smaller : Subgroup G, smaller ≤ lift → IsSubnormal smaller ⊤ →
        smaller.map (QuotientGroup.mk' (componentClassificationOddCore G)) = component →
        smaller = lift := by
  let : Group.IsPerfect component := ⟨hcomponent.2.2.1⟩
  obtain ⟨lift, hsubnormal, hmap, hperfect, hminimal⟩ := perfect_subnormal_lift
    (QuotientGroup.mk' (componentClassificationOddCore G))
    (QuotientGroup.mk'_surjective (componentClassificationOddCore G)) component
    (mathlib_subnormal_of_chain hcomponent.2.1 Subgroup.IsSubnormal.top)
  refine ⟨lift, hsubnormal, hmap, hperfect, ?_, hminimal⟩
  apply (quotient_component_iff lift hsubnormal).mp
  rw [hmap]
  exact hcomponent

theorem componentType_iff_perfect_local_lift (G : Type*) [Group G] [Finite G] :
    componentClassificationComponentType G ↔
      ∃ (involution : G) (_ : orderOf involution = 2)
        (lift : Subgroup (Subgroup.centralizer ({involution} : Set G))),
        IsSubnormal lift ⊤ ∧ commutator lift = ⊤ ∧
          IsQuasisimple (lift ⧸ componentClassificationOddCore lift) := by
  constructor
  · rintro ⟨involution, hinvolution, component, hcomponent⟩
    obtain ⟨lift, hsubnormal, _, hperfect, hquasisimple, _⟩ :=
      perfect_lift_of_component component hcomponent
    exact ⟨involution, hinvolution, lift, hsubnormal, hperfect, hquasisimple⟩
  · rintro ⟨involution, hinvolution, lift, hsubnormal, _, hquasisimple⟩
    exact ⟨involution, hinvolution,
      lift.map (QuotientGroup.mk' (componentClassificationOddCore
        (Subgroup.centralizer ({involution} : Set G)))),
      (quotient_component_iff lift hsubnormal).mpr hquasisimple⟩

end CFSG.ComponentClassification.Components
