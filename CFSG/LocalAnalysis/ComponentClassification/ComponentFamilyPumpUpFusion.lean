module

public import CFSG.LocalAnalysis.ComponentClassification.InvolutionLayerOrbitLocation

public section

open CFSG.Open

namespace CFSG.ComponentClassification.ComponentFamilyPumpUpFusion

theorem exists_outside_two {Index : Type*} [Fintype Index]
    (hcard : 3 ≤ Fintype.card Index) (first second : Index) :
    ∃ other : Index, other ≠ first ∧ other ≠ second := by
  classical
  let remainder := (Finset.univ.erase first).erase second
  have hfirstCard : (Finset.univ.erase first).card = Fintype.card Index - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have hpositive : 0 < remainder.card := by
    by_cases hsecond : second ∈ Finset.univ.erase first
    · have hcardRemainder := Finset.card_erase_of_mem hsecond
      change remainder.card = (Finset.univ.erase first).card - 1 at hcardRemainder
      omega
    · have heq : remainder = Finset.univ.erase first := Finset.erase_eq_of_notMem hsecond
      rw [heq, hfirstCard]
      omega
  obtain ⟨other, hother⟩ := Finset.card_pos.mp hpositive
  exact ⟨other, (Finset.mem_erase.mp (Finset.mem_erase.mp hother).2).1,
    (Finset.mem_erase.mp hother).1⟩

theorem invariant_lift {G : Type*} [Group G] [Finite G] {Index : Type*} [Fintype Index]
    (factors : Index → Subgroup G)
    (hcommutes : Pairwise (fun first second => ⁅factors first, factors second⁆ = ⊥))
    (hcard : 3 ≤ Fintype.card Index) (overgroup : Subgroup G) (anchor : Index)
    (hanchorLe : factors anchor ≤ overgroup)
    (hanchor : IsComponentOf ((factors anchor).subgroupOf overgroup) ⊤)
    (containing component : Subgroup G) (hcontainingLe : containing ≤ overgroup)
    (hcontaining : IsComponentOf (containing.subgroupOf overgroup) ⊤)
    (hcontained : component ≤ containing) :
    ∃ index : Index, ⁅component, factors index⁆ = ⊥ := by
  by_cases heq : containing = factors anchor
  · obtain ⟨other, hother, _⟩ := exists_outside_two hcard anchor anchor
    refine ⟨other, ?_⟩
    apply le_bot_iff.mp
    have hbound := Subgroup.commutator_mono (hcontained.trans heq.le) (le_rfl : factors other ≤ factors other)
    rw [hcommutes (Ne.symm hother)] at hbound
    exact hbound
  · refine ⟨anchor, ?_⟩
    apply le_bot_iff.mp
    have hbound := Subgroup.commutator_mono hcontained (le_rfl : factors anchor ≤ factors anchor)
    rw [OrdinaryComponentTransport.commute_local_distinct containing (factors anchor) overgroup
      hcontainingLe hanchorLe hcontaining hanchor heq] at hbound
    exact hbound

theorem diagonal_lift {G : Type*} [Group G] [Finite G] {Index : Type*} [Fintype Index]
    (factors : Index → Subgroup G) (hinjective : Function.Injective factors)
    (hcommutes : Pairwise (fun first second => ⁅factors first, factors second⁆ = ⊥))
    (hcard : 3 ≤ Fintype.card Index) (overgroup : Subgroup G) (anchor : Index)
    (hanchorLe : factors anchor ≤ overgroup)
    (hanchor : IsComponentOf ((factors anchor).subgroupOf overgroup) ⊤)
    (automorphism : MulAut G)
    (hpreserves : ∀ index, ∃ imageIndex, (factors index).map automorphism.toMonoidHom = factors imageIndex)
    (containing component : Subgroup G)
    (hcontainingLe : containing ≤ overgroup)
    (hcontainingImageLe : containing.map automorphism.toMonoidHom ≤ overgroup)
    (hcontaining : IsComponentOf (containing.subgroupOf overgroup) ⊤)
    (hcontainingImage : IsComponentOf ((containing.map automorphism.toMonoidHom).subgroupOf overgroup) ⊤)
    (hcontained : component ≤ containing ⊔ containing.map automorphism.toMonoidHom) :
    ∃ index : Index, ⁅component, factors index⁆ = ⊥ := by
  classical
  let partner := containing.map automorphism.toMonoidHom
  by_cases hfirst : containing = factors anchor
  · obtain ⟨second, hsecond⟩ := hpreserves anchor
    have hpartner : partner = factors second := by
      change containing.map automorphism.toMonoidHom = factors second
      rw [hfirst]
      exact hsecond
    obtain ⟨other, hotherFirst, hotherSecond⟩ := exists_outside_two hcard anchor second
    refine ⟨other, ?_⟩
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    apply hcontained.trans
    apply sup_le
    · rw [hfirst]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcommutes (Ne.symm hotherFirst))
    · rw [show containing.map automorphism.toMonoidHom = factors second from hpartner]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcommutes (Ne.symm hotherSecond))
  · by_cases hsecond : partner = factors anchor
    · have hcontainingMember : ∃ first, containing = factors first := by
        let image : Index → Index := fun index => Classical.choose (hpreserves index)
        have himage : Function.Injective image := by
          intro first second heq
          apply hinjective
          apply Subgroup.map_injective (f := automorphism.toMonoidHom) automorphism.injective
          rw [Classical.choose_spec (hpreserves first), Classical.choose_spec (hpreserves second)]
          exact congrArg factors heq
        obtain ⟨preimage, hpreimage⟩ := (Finite.surjective_of_injective himage) anchor
        have heq := Classical.choose_spec (hpreserves preimage)
        change (factors preimage).map automorphism.toMonoidHom = factors (image preimage) at heq
        rw [hpreimage] at heq
        refine ⟨preimage, ?_⟩
        apply Subgroup.map_injective (f := automorphism.toMonoidHom) automorphism.injective
        exact hsecond.trans heq.symm
      obtain ⟨first, hfirstMember⟩ := hcontainingMember
      obtain ⟨other, hotherFirst, hotherSecond⟩ := exists_outside_two hcard first anchor
      refine ⟨other, ?_⟩
      apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      apply hcontained.trans
      apply sup_le
      · rw [hfirstMember]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcommutes (Ne.symm hotherFirst))
      · rw [show containing.map automorphism.toMonoidHom = factors anchor from hsecond]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcommutes (Ne.symm hotherSecond))
    · refine ⟨anchor, ?_⟩
      apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      apply hcontained.trans
      apply sup_le
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (OrdinaryComponentTransport.commute_local_distinct containing (factors anchor) overgroup
            hcontainingLe hanchorLe hcontaining hanchor hfirst)
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (OrdinaryComponentTransport.commute_local_distinct partner (factors anchor) overgroup
            hcontainingImageLe hanchorLe hcontainingImage hanchor hsecond)

theorem of_local_layer {G : Type*} [Group G] [Finite G] {Index : Type*} [Fintype Index]
    (factors : Index → Subgroup G) (hinjective : Function.Injective factors)
    (hcommutes : Pairwise (fun first second => ⁅factors first, factors second⁆ = ⊥))
    (hcard : 3 ≤ Fintype.card Index) (overgroup : Subgroup G) (anchor : Index)
    (hanchorLe : factors anchor ≤ overgroup)
    (hanchor : IsComponentOf ((factors anchor).subgroupOf overgroup) ⊤)
    (element : overgroup) (hsquare : element * element = 1)
    (hpreserves : ∀ index, ∃ imageIndex,
      (factors index).map (MulAut.conj element.val).toMonoidHom = factors imageIndex)
    (component : Subgroup G) (hcomponentLe : component ≤ overgroup)
    (hcentralizer : component.subgroupOf overgroup ≤ Subgroup.centralizer {element})
    (hcomponent : IsComponentOf ((component.subgroupOf overgroup).subgroupOf
      (Subgroup.centralizer {element})) ⊤)
    (hlayer : component.subgroupOf overgroup ≤ Layer.subgroup overgroup) :
    ∃ index : Index, ⁅component, factors index⁆ = ⊥ := by
  obtain ⟨intrinsic, hintrinsic, hcase⟩ := InvolutionLayerOrbitLocation.location element hsquare
    (component.subgroupOf overgroup) hcentralizer hcomponent hlayer
  let containing := intrinsic.map overgroup.subtype
  have hcontainingLe : containing ≤ overgroup := Subgroup.map_subtype_le _
  have hcontaining : IsComponentOf (containing.subgroupOf overgroup) ⊤ :=
    OrdinaryComponentTransport.subtype_image_component overgroup intrinsic hintrinsic
  have hequivariance : overgroup.subtype.comp (MulAut.conj element).toMonoidHom =
      (MulAut.conj element.val).toMonoidHom.comp overgroup.subtype := by
    ext member
    rfl
  rcases hcase with ⟨_, hle, _⟩ | ⟨hfactorCommutes, _, hdiagonal⟩
  · have hambient := Subgroup.map_mono (f := overgroup.subtype) hle
    rw [Subgroup.map_subgroupOf_eq_of_le hcomponentLe] at hambient
    exact invariant_lift factors hcommutes hcard overgroup anchor hanchorLe hanchor
      containing component hcontainingLe hcontaining hambient
  · have hlocalCover : component.subgroupOf overgroup ≤
        intrinsic ⊔ intrinsic.map (MulAut.conj element).toMonoidHom := by
      rw [hdiagonal]
      exact (CFSG.ComponentClassification.SwappedQuasisimpleProduct.diagonal_le_fixed
        intrinsic (MulAut.conj element) (by
          intro member
          have hconjSquare : MulAut.conj element * MulAut.conj element = 1 := by
            rw [← map_mul, hsquare, map_one]
          exact congrArg (fun automorphism : MulAut overgroup => automorphism member) hconjSquare)
          hfactorCommutes).trans inf_le_left
    have hambientCover := Subgroup.map_mono (f := overgroup.subtype) hlocalCover
    rw [Subgroup.map_subgroupOf_eq_of_le hcomponentLe, Subgroup.map_sup, Subgroup.map_map,
      hequivariance, ← Subgroup.map_map] at hambientCover
    let intrinsicPartner := intrinsic.map (MulAut.conj element).toMonoidHom
    have hpartner : IsComponentOf intrinsicPartner ⊤ :=
      (LocalComponents.equiv_iff (MulAut.conj element) intrinsic).mpr hintrinsic
    have hpartnerMap : intrinsicPartner.map overgroup.subtype =
        containing.map (MulAut.conj element.val).toMonoidHom := by
      change (intrinsic.map (MulAut.conj element).toMonoidHom).map overgroup.subtype = _
      rw [Subgroup.map_map, hequivariance, ← Subgroup.map_map]
    have hpartnerLe : containing.map (MulAut.conj element.val).toMonoidHom ≤ overgroup := by
      rw [← hpartnerMap]
      exact Subgroup.map_subtype_le _
    have hpartnerComponent : IsComponentOf ((containing.map (MulAut.conj element.val).toMonoidHom).subgroupOf
        overgroup) ⊤ := by
      rw [← hpartnerMap]
      exact OrdinaryComponentTransport.subtype_image_component overgroup intrinsicPartner hpartner
    exact diagonal_lift factors hinjective hcommutes hcard overgroup anchor hanchorLe hanchor
      (MulAut.conj element.val) hpreserves containing component hcontainingLe hpartnerLe
      hcontaining hpartnerComponent hambientCover

end CFSG.ComponentClassification.ComponentFamilyPumpUpFusion
