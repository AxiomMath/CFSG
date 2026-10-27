module

public import CFSG.LocalAnalysis.ComponentClassification.InvolutionFixedPoints
public import CFSG.LocalAnalysis.ComponentClassification.PerfectPermutationActions

public section

open CFSG.Open

namespace CFSG.ComponentClassification.ComponentAutomorphisms

@[expose] noncomputable def subgroupAction {A G : Type*} [Group A] [Group G]
    (action : A →* MulAut G) : A →* Equiv.Perm (Subgroup G) :=
  { toFun := fun actor => (action actor).mapSubgroup.toEquiv
    map_one' := by
      apply Equiv.ext
      intro subgroup
      change subgroup.map (action 1).toMonoidHom = subgroup
      rw [map_one]
      exact Subgroup.map_id subgroup
    map_mul' := by
      intro left right
      apply Equiv.ext
      intro subgroup
      change subgroup.map (action (left * right)).toMonoidHom =
        (subgroup.map (action right).toMonoidHom).map (action left).toMonoidHom
      rw [Subgroup.map_map, map_mul]
      rfl }

theorem center_le_layer_center {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (hcomponent : IsComponentOf component ⊤) :
    (Subgroup.center component).map component.subtype ≤
      Subgroup.centralizer (Layer.subgroup G : Set G) := by
  apply Subgroup.le_centralizer_iff.mpr
  apply sSup_le
  intro other hother
  by_cases heq : other = component
  · subst other
    intro member hmember
    apply Subgroup.mem_centralizer_iff.mpr
    intro central hcentral
    obtain ⟨lift, hlift, rfl⟩ := Subgroup.mem_map.mp hcentral
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hlift (⟨member, hmember⟩ : component)).symm
  · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (LocalComponents.commute_of_ne other component hother hcomponent heq)).trans
      (Subgroup.centralizer_le (Subgroup.map_subtype_le _))

theorem center_le_center_of_layer_top {G : Type*} [Group G] [Finite G]
    (hlayer : Layer.subgroup G = ⊤) (component : Subgroup G)
    (hcomponent : IsComponentOf component ⊤) :
    (Subgroup.center component).map component.subtype ≤ Subgroup.center G := by
  have hcentralizes := center_le_layer_center component hcomponent
  rw [hlayer] at hcentralizes
  intro member hmember
  apply Subgroup.mem_center_iff.mpr
  intro other
  exact Subgroup.mem_centralizer_iff.mp (hcentralizes hmember) other (Subgroup.mem_top other)

theorem image_in_involution_pair {A G : Type*} [Group A] [Group.IsPerfect A] [Group G] [Finite G]
    (hlayer : Layer.subgroup G = ⊤) (action : A →* MulAut G) (automorphism : MulAut G)
    (hinvolutive : Function.Involutive automorphism)
    (hcommutes : ∀ actor : A, Commute automorphism (action actor))
    (hcenter : ∀ actor : A, ∀ member ∈ Subgroup.center G, (action actor) member = member)
    (hfixed : ∀ actor : A, ∀ member : G, automorphism member = member →
      (action actor) member = member)
    (component : Subgroup G) (hcomponent : IsComponentOf component ⊤) (actor : A) :
    component.map (action actor).toMonoidHom = component ∨
      component.map (action actor).toMonoidHom = component.map automorphism.toMonoidHom := by
  classical
  let partner := component.map automorphism.toMonoidHom
  let image := component.map (action actor).toMonoidHom
  have hpartner : IsComponentOf partner ⊤ := (LocalComponents.equiv_iff automorphism component).mpr
    hcomponent
  have himage : IsComponentOf image ⊤ := (LocalComponents.equiv_iff (action actor) component).mpr
    hcomponent
  have hfull := FixedCentralPreimage.fixed_of_perfect_action action automorphism hcommutes
    hcenter hfixed
  by_cases hpartnerEq : partner = component
  · have hcomponentInvariant : component.map automorphism.toMonoidHom = component := hpartnerEq
    let restricted := (automorphism.subgroupMap component).trans
      (MulEquiv.subgroupCongr hcomponentInvariant)
    have hrestrictedInvolutive : Function.Involutive restricted := by
      intro member
      apply Subtype.ext
      exact hinvolutive member.val
    obtain ⟨member, hnotCentral, hliftedFixed⟩ :=
      InvolutionFixedPoints.exists_noncentral_lifted_fixed hcomponent.2.2 restricted hrestrictedInvolutive
    have hcentral : member.val⁻¹ * automorphism member.val ∈ Subgroup.center G := by
      have hlocal := (FixedCentralPreimage.mem_iff restricted member).mp hliftedFixed
      exact center_le_center_of_layer_top hlayer component hcomponent
        (Subgroup.mem_map_of_mem component.subtype hlocal)
    have hmemberFixed := hfull actor member.val ((FixedCentralPreimage.mem_iff automorphism _).mpr hcentral)
    left
    by_contra hne
    have hmemberImage : member.val ∈ image := by
      rw [← hmemberFixed]
      exact Subgroup.mem_map_of_mem (action actor).toMonoidHom member.property
    have hcentralizes := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (LocalComponents.commute_of_ne image component himage hcomponent hne)
    apply hnotCentral
    apply Subgroup.mem_center_iff.mpr
    intro other
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcentralizes hmemberImage)
      other.val other.property)
  · by_contra hneither
    have himageNe : image ≠ component := fun heq => hneither (Or.inl heq)
    have himagePartnerNe : image ≠ partner := fun heq => hneither (Or.inr heq)
    let partnerImage := partner.map (action actor).toMonoidHom
    have hpartnerImage : IsComponentOf partnerImage ⊤ :=
      (LocalComponents.equiv_iff (action actor) partner).mpr hpartner
    have hpartnerImageNe : partnerImage ≠ component := by
      intro heq
      have hmap := congrArg (Subgroup.map automorphism.toMonoidHom) heq
      have hconjugate : partnerImage.map automorphism.toMonoidHom = image := by
        rw [Subgroup.map_map, Subgroup.map_map]
        have hcomposite : (automorphism.toMonoidHom.comp
            (action actor).toMonoidHom).comp automorphism.toMonoidHom = (action actor).toMonoidHom := by
          apply MonoidHom.ext
          intro member
          have hcommutation := congrArg (fun transformation : MulAut G => transformation
            (automorphism member)) (hcommutes actor).eq
          change automorphism ((action actor) (automorphism member)) =
            (action actor) (automorphism (automorphism member)) at hcommutation
          rwa [hinvolutive] at hcommutation
        rw [hcomposite]
      rw [hconjugate] at hmap
      exact himagePartnerNe hmap
    have hnoncommutative : ¬ IsMulCommutative component := by
      let : Group.IsPerfect component := ⟨hcomponent.2.2.1⟩
      let : Nontrivial component := Quasisimple.nontrivial hcomponent.2.2
      exact Group.IsPerfect.not_isMulCommutative component
    obtain ⟨member, hnotCentral⟩ : ∃ member : component, member ∉ Subgroup.center component := by
      by_contra hnone
      apply hnoncommutative
      apply isMulCommutative_iff.mpr
      intro left right
      have hcenterMember : right ∈ Subgroup.center component := by
        by_contra hnotCenter
        exact hnone ⟨right, hnotCenter⟩
      exact Subgroup.mem_center_iff.mp hcenterMember left
    have hpartnerMem : automorphism member.val ∈ partner :=
      Subgroup.mem_map_of_mem automorphism.toMonoidHom member.property
    have hcomponentPartnerCommutes := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (LocalComponents.commute_of_ne component partner hcomponent hpartner (Ne.symm hpartnerEq))
    have hmembersCommute := Subgroup.mem_centralizer_iff.mp
      (hcomponentPartnerCommutes member.property) (automorphism member.val) hpartnerMem
    have hproductFixed : automorphism (member.val * automorphism member.val) =
        member.val * automorphism member.val := by
      rw [map_mul, hinvolutive]
      exact hmembersCommute
    have hactorFixed := hfixed actor _ hproductFixed
    have hproductImage : (action actor) (member.val * automorphism member.val) ∈
        Subgroup.centralizer (component : Set G) := by
      rw [map_mul]
      apply Subgroup.mul_mem
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (LocalComponents.commute_of_ne image component himage hcomponent himageNe)
          (Subgroup.mem_map_of_mem (action actor).toMonoidHom member.property)
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (LocalComponents.commute_of_ne partnerImage component hpartnerImage hcomponent hpartnerImageNe)
          (Subgroup.mem_map_of_mem (action actor).toMonoidHom hpartnerMem)
    rw [hactorFixed] at hproductImage
    have hpartnerCentralizes := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (LocalComponents.commute_of_ne partner component hpartner hcomponent hpartnerEq) hpartnerMem
    have hmemberCentralizes : member.val ∈ Subgroup.centralizer (component : Set G) := by
      have hmul := (Subgroup.centralizer (component : Set G)).mul_mem hproductImage
        ((Subgroup.centralizer (component : Set G)).inv_mem hpartnerCentralizes)
      simpa only [mul_inv_cancel_right] using hmul
    apply hnotCentral
    apply Subgroup.mem_center_iff.mpr
    intro other
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hmemberCentralizes other.val other.property)

theorem component_image_eq_self {A G : Type*} [Group A] [Group.IsPerfect A] [Group G] [Finite G]
    (hlayer : Layer.subgroup G = ⊤) (action : A →* MulAut G) (automorphism : MulAut G)
    (hinvolutive : Function.Involutive automorphism)
    (hcommutes : ∀ actor : A, Commute automorphism (action actor))
    (hcenter : ∀ actor : A, ∀ member ∈ Subgroup.center G, (action actor) member = member)
    (hfixed : ∀ actor : A, ∀ member : G, automorphism member = member →
      (action actor) member = member)
    (component : Subgroup G) (hcomponent : IsComponentOf component ⊤) (actor : A) :
    component.map (action actor).toMonoidHom = component := by
  classical
  let partner := component.map automorphism.toMonoidHom
  let invariantSet : Set (Subgroup G) := {component, partner}
  have hpartner : IsComponentOf partner ⊤ := (LocalComponents.equiv_iff automorphism component).mpr
    hcomponent
  have hpartnerDouble : partner.map automorphism.toMonoidHom = component := by
    rw [Subgroup.map_map]
    have hcomposite : automorphism.toMonoidHom.comp automorphism.toMonoidHom = MonoidHom.id G := by
      apply MonoidHom.ext
      exact hinvolutive
    rw [hcomposite, Subgroup.map_id]
  have hforward : ∀ acting : A, ∀ member ∈ invariantSet,
      subgroupAction action acting member ∈ invariantSet := by
    intro acting member hmember
    rcases Set.mem_insert_iff.mp hmember with hcomponentMem | hpartnerMem
    · subst member
      rcases image_in_involution_pair hlayer action automorphism hinvolutive hcommutes hcenter hfixed
        component hcomponent acting with heq | heq
      · change component.map (action acting).toMonoidHom ∈ invariantSet
        rw [heq]
        exact Set.mem_insert _ _
      · change component.map (action acting).toMonoidHom ∈ invariantSet
        rw [heq]
        exact Set.mem_insert_of_mem _ (Set.mem_singleton partner)
    · have heq : member = partner := Set.mem_singleton_iff.mp hpartnerMem
      subst member
      rcases image_in_involution_pair hlayer action automorphism hinvolutive hcommutes hcenter hfixed
        partner hpartner acting with heq | heq
      · change partner.map (action acting).toMonoidHom ∈ invariantSet
        rw [heq]
        exact Set.mem_insert_of_mem _ (Set.mem_singleton partner)
      · change partner.map (action acting).toMonoidHom ∈ invariantSet
        rw [heq, hpartnerDouble]
        exact Set.mem_insert _ _
  have hinvariant : ∀ acting : A, ∀ member : Subgroup G,
      subgroupAction action acting member ∈ invariantSet ↔ member ∈ invariantSet := by
    intro acting member
    refine ⟨?_, hforward acting member⟩
    intro hmem
    have hinverse := hforward acting⁻¹ (subgroupAction action acting member) hmem
    rw [map_inv] at hinverse
    simpa only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply] using hinverse
  let : Finite invariantSet := (Set.toFinite invariantSet).to_subtype
  have hcard : Nat.card invariantSet ≤ 2 := by
    let covering : Bool → invariantSet := fun choice =>
      if choice then ⟨component, Set.mem_insert _ _⟩
        else ⟨partner, Set.mem_insert_of_mem _ (Set.mem_singleton partner)⟩
    have hsurjective : Function.Surjective covering := by
      intro member
      rcases Set.mem_insert_iff.mp member.property with hfirst | hsecond
      · exact ⟨true, Subtype.ext hfirst.symm⟩
      · exact ⟨false, Subtype.ext (Set.mem_singleton_iff.mp hsecond).symm⟩
    simpa using Nat.card_le_card_of_surjective covering hsurjective
  exact PerfectPermutationActions.fixed_on_small_invariant (subgroupAction action) invariantSet
    hcard hinvariant actor component (Set.mem_insert _ _)

theorem component_image_eq_self_on_layer {A G : Type*} [Group A] [Group.IsPerfect A]
    [Group G] [Finite G] (action : A →* MulAut G) (automorphism : MulAut G)
    (hinvolutive : Function.Involutive automorphism)
    (hcommutes : ∀ actor : A, Commute automorphism (action actor))
    (hcenter : ∀ actor : A, ∀ member : Layer.subgroup G,
      member ∈ Subgroup.center (Layer.subgroup G) → (action actor) member.val = member.val)
    (hfixed : ∀ actor : A, ∀ member ∈ Layer.subgroup G, automorphism member = member →
      (action actor) member = member)
    (component : Subgroup G) (hcomponent : IsComponentOf component ⊤) (actor : A) :
    component.map (action actor).toMonoidHom = component := by
  let layer := Layer.subgroup G
  let : layer.Characteristic := Layer.characteristic G
  let restriction : MulAut G →* MulAut layer := MulAut.characteristic layer
  let restrictedAction : A →* MulAut layer := restriction.comp action
  let restrictedAutomorphism : MulAut layer := restriction automorphism
  have hrestrictedInvolutive : Function.Involutive restrictedAutomorphism := by
    intro member
    apply Subtype.ext
    change ↑((MulAut.characteristic layer automorphism)
      ((MulAut.characteristic layer automorphism) member)) = member.val
    rw [MulAut.characteristic_apply_apply_coe, MulAut.characteristic_apply_apply_coe]
    exact hinvolutive member.val
  have hrestrictedCommutes : ∀ acting : A,
      Commute restrictedAutomorphism (restrictedAction acting) := by
    intro acting
    exact (hcommutes acting).map restriction
  have hrestrictedCenter : ∀ acting : A, ∀ member ∈ Subgroup.center layer,
      (restrictedAction acting) member = member := by
    intro acting member hmember
    apply Subtype.ext
    exact hcenter acting member hmember
  have hrestrictedFixed : ∀ acting : A, ∀ member : layer,
      restrictedAutomorphism member = member → (restrictedAction acting) member = member := by
    intro acting member hmember
    apply Subtype.ext
    exact hfixed acting member.val member.property (congrArg Subtype.val hmember)
  have hle : component ≤ layer := Layer.component_le hcomponent
  have hlocal := component_image_eq_self (Layer.layer_top G) restrictedAction
    restrictedAutomorphism hrestrictedInvolutive hrestrictedCommutes hrestrictedCenter
    hrestrictedFixed (component.subgroupOf layer) (LocalComponents.of_overgroup hcomponent hle) actor
  have hmap := congrArg (Subgroup.map layer.subtype) hlocal
  have hcomposite : layer.subtype.comp (restrictedAction actor).toMonoidHom =
      (action actor).toMonoidHom.comp layer.subtype := by
    apply MonoidHom.ext
    intro member
    exact MulAut.characteristic_apply_apply_coe layer (action actor) member
  rw [Subgroup.map_map, hcomposite, ← Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le hle] at hmap
  exact hmap

theorem ambient_normalizes_components {G : Type*} [Group G] [Finite G]
    (perfectSubgroup : Subgroup G) [Group.IsPerfect perfectSubgroup] (element : G)
    (hsquare : element * element = 1)
    (hcentralizesElement : perfectSubgroup ≤ Subgroup.centralizer ({element} : Set G))
    (hcentralizesCenter : ⁅perfectSubgroup, (Subgroup.center (Layer.subgroup G)).map
      (Layer.subgroup G).subtype⁆ = ⊥)
    (hcentralizesFixed : ⁅perfectSubgroup,
      Layer.subgroup G ⊓ Subgroup.centralizer ({element} : Set G)⁆ = ⊥)
    (component : Subgroup G) (hcomponent : IsComponentOf component ⊤) :
    perfectSubgroup ≤ Subgroup.normalizer (component : Set G) := by
  let action : perfectSubgroup →* MulAut G := MulAut.conj.comp perfectSubgroup.subtype
  let automorphism : MulAut G := MulAut.conj element
  have hinvolutive : Function.Involutive automorphism := by
    intro member
    have htwice : automorphism * automorphism = 1 := by
      change MulAut.conj element * MulAut.conj element = 1
      rw [← map_mul, hsquare, map_one]
    exact congrArg (fun value : MulAut G => value member) htwice
  have hcommutes : ∀ actor : perfectSubgroup, Commute automorphism (action actor) := by
    intro actor
    have heq := Subgroup.mem_centralizer_singleton_iff.mp
      (hcentralizesElement actor.property)
    exact (show Commute element actor.val from heq.symm).map MulAut.conj
  have hcenter : ∀ actor : perfectSubgroup, ∀ member : Layer.subgroup G,
      member ∈ Subgroup.center (Layer.subgroup G) → (action actor) member.val = member.val := by
    intro actor member hmember
    have heq := Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcentralizesCenter actor.property)
        member.val (Subgroup.mem_map_of_mem (Layer.subgroup G).subtype hmember)
    change actor.val * member.val * actor.val⁻¹ = member.val
    rw [← heq]
    group
  have hfixed : ∀ actor : perfectSubgroup, ∀ member ∈ Layer.subgroup G,
      automorphism member = member → (action actor) member = member := by
    intro actor member hmember hmemberFixed
    have hcentralizer : member ∈ Subgroup.centralizer ({element} : Set G) := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      change element * member * element⁻¹ = member at hmemberFixed
      calc
        member * element = (element * member * element⁻¹) * element := by rw [hmemberFixed]
        _ = element * member := by group
    have heq := Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcentralizesFixed actor.property)
        member ⟨hmember, hcentralizer⟩
    change actor.val * member * actor.val⁻¹ = member
    rw [← heq]
    group
  intro actor hactor
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  exact component_image_eq_self_on_layer action automorphism hinvolutive hcommutes hcenter hfixed
    component hcomponent (⟨actor, hactor⟩ : perfectSubgroup)

end CFSG.ComponentClassification.ComponentAutomorphisms
