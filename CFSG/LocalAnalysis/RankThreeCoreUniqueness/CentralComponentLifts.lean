module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralPerfectLifts
public import CFSG.Assembly.Subnormal

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem map_center_eq_of_mulEquiv
    {G Image : Type*} [Group G] [Group Image] (equivalence : G ≃* Image) :
    Subgroup.map equivalence.toMonoidHom (Subgroup.center G) = Subgroup.center Image := by
  apply le_antisymm
  · rintro element ⟨preimage, hpreimage, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro other
    obtain ⟨otherPreimage, rfl⟩ := equivalence.surjective other
    change equivalence otherPreimage * equivalence preimage =
      equivalence preimage * equivalence otherPreimage
    simpa only [map_mul] using congrArg equivalence
      (Subgroup.mem_center_iff.mp hpreimage otherPreimage)
  · intro element helement
    refine ⟨equivalence.symm element, ?_, equivalence.apply_symm_apply element⟩
    apply Subgroup.mem_center_iff.mpr
    intro other
    apply equivalence.injective
    simpa only [map_mul, MulEquiv.apply_symm_apply] using
      Subgroup.mem_center_iff.mp helement (equivalence other)

noncomputable def centerQuotientEquiv
    {G Image : Type*} [Group G] [Group Image] (equivalence : G ≃* Image) :
    (G ⧸ Subgroup.center G) ≃* (Image ⧸ Subgroup.center Image) :=
  QuotientGroup.congr (Subgroup.center G) (Subgroup.center Image) equivalence
    (map_center_eq_of_mulEquiv equivalence)

theorem quasisimple_of_mulEquiv
    {G Image : Type*} [Group G] [Group Image] (equivalence : G ≃* Image)
    (hquasisimple : IsQuasisimple G) : IsQuasisimple Image :=
  hquasisimple.of_mulEquiv equivalence.symm

theorem mapped_internal_normal_subgroup_normal_subgroupOf
    {G : Type*} [Group G] (overgroup : Subgroup G)
    (internalGroup : Subgroup overgroup) (hnormal : internalGroup.Normal) :
    ((Subgroup.map overgroup.subtype internalGroup).subgroupOf overgroup).Normal := by
  change (Subgroup.comap overgroup.subtype
    (Subgroup.map overgroup.subtype internalGroup)).Normal
  rw [Subgroup.comap_map_eq,
    MonoidHom.ker_eq_bot overgroup.subtype overgroup.subtype_injective]
  simpa only [sup_bot_eq] using hnormal

theorem normal_quasisimple_internal_subgroup_maps_to_component
    {G : Type*} [Group G] (overgroup : Subgroup G) (hovergroupNormal : overgroup.Normal)
    (internalGroup : Subgroup overgroup) (hnormal : internalGroup.Normal)
    (hquasisimple : IsQuasisimple internalGroup) :
    IsComponentOf (Subgroup.map overgroup.subtype internalGroup) ⊤ := by
  let : overgroup.Normal := hovergroupNormal
  refine ⟨le_top, ?_, ?_⟩
  · exact IsSubnormal.step (Subgroup.map_subtype_le _)
      (mapped_internal_normal_subgroup_normal_subgroupOf overgroup internalGroup hnormal)
      (IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤))
  · exact quasisimple_of_mulEquiv
      (internalGroup.equivMapOfInjective overgroup.subtype overgroup.subtype_injective)
      hquasisimple

theorem normal_subgroupOf_map
    {G Image : Type*} [Group G] [Group Image]
    (homomorphism : G →* Image)
    (subgroup overgroup : Subgroup G) (hbound : subgroup ≤ overgroup)
    (hnormal : (subgroup.subgroupOf overgroup).Normal) :
    ((Subgroup.map homomorphism subgroup).subgroupOf
      (Subgroup.map homomorphism overgroup)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hbound)).mpr
  intro element conjugator helement hconjugator
  obtain ⟨preimage, hpreimage, rfl⟩ := helement
  obtain ⟨conjugatorPreimage, hconjugatorPreimage, rfl⟩ := hconjugator
  have hconjugate := (Subgroup.normal_subgroupOf_iff hbound).mp hnormal
    preimage conjugatorPreimage hpreimage hconjugatorPreimage
  exact ⟨conjugatorPreimage * preimage * conjugatorPreimage⁻¹, hconjugate,
    by simp only [map_mul, map_inv]⟩

theorem cfsg_isSubnormal_map
    {G Image : Type*} [Group G] [Group Image]
    (homomorphism : G →* Image)
    {subgroup overgroup : Subgroup G} (hsubnormal : IsSubnormal subgroup overgroup) :
    IsSubnormal (Subgroup.map homomorphism subgroup) (Subgroup.map homomorphism overgroup) :=
  hsubnormal.map homomorphism

theorem cfsg_isSubnormal_trans
    {G : Type*} [Group G] {subgroup intermediate overgroup : Subgroup G}
    (hfirst : IsSubnormal subgroup intermediate) (hsecond : IsSubnormal intermediate overgroup) :
    IsSubnormal subgroup overgroup :=
  hfirst.trans hsecond

theorem component_internal_normal_overgroup_maps_to_component
    {G : Type*} [Group G] (overgroup : Subgroup G) (hovergroupNormal : overgroup.Normal)
    (component : Subgroup overgroup) (hcomponent : IsComponentOf component ⊤) :
    IsComponentOf (Subgroup.map overgroup.subtype component) ⊤ := by
  let : overgroup.Normal := hovergroupNormal
  refine ⟨le_top, ?_, ?_⟩
  · have hmapped := cfsg_isSubnormal_map overgroup.subtype hcomponent.2.1
    have htop : Subgroup.map overgroup.subtype ⊤ = overgroup := by
      apply le_antisymm (Subgroup.map_subtype_le _)
      intro element helement
      exact ⟨⟨element, helement⟩, Subgroup.mem_top _, rfl⟩
    rw [htop] at hmapped
    exact cfsg_isSubnormal_trans hmapped
      (IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤))
  · exact quasisimple_of_mulEquiv
      (component.equivMapOfInjective overgroup.subtype overgroup.subtype_injective)
      hcomponent.2.2

theorem central_extension_normal_simple_factor_has_normal_quasisimple_lift
    {G Image : Type*} [Group G] [Group Image]
    (homomorphism : G →* Image) (hsurjective : Function.Surjective homomorphism)
    (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (simpleFactor : Subgroup Image) (hnormal : simpleFactor.Normal)
    (hsimple : IsSimpleGroup simpleFactor)
    (hnonab : ∃ first second : simpleFactor, first * second ≠ second * first) :
    ∃ liftedGroup : Subgroup G, liftedGroup.Normal ∧ IsQuasisimple liftedGroup ∧
      Nonempty ((liftedGroup ⧸ Subgroup.center liftedGroup) ≃* simpleFactor) := by
  let : simpleFactor.Normal := hnormal
  let : IsSimpleGroup simpleFactor := hsimple
  let preimageGroup := Subgroup.comap homomorphism simpleFactor
  let : preimageGroup.Normal := hnormal.comap homomorphism
  let restrictedMap : preimageGroup →* simpleFactor :=
    (homomorphism.comp preimageGroup.subtype).codRestrict simpleFactor
      (fun element => element.property)
  have hrestrictedSurjective : Function.Surjective restrictedMap := by
    intro element
    obtain ⟨preimage, hpreimage⟩ := hsurjective element.val
    have hmem : preimage ∈ preimageGroup := by
      change homomorphism preimage ∈ simpleFactor
      rw [hpreimage]
      exact element.property
    exact ⟨⟨preimage, hmem⟩, Subtype.ext hpreimage⟩
  have hrestrictedCentral : restrictedMap.ker ≤ Subgroup.center preimageGroup := by
    intro element helement
    have hkernel : element.val ∈ homomorphism.ker := by
      change homomorphism element.val = 1
      exact congrArg Subtype.val helement
    apply Subgroup.mem_center_iff.mpr
    intro other
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hcentral hkernel) other.val
  obtain ⟨hderivedQuasisimple, hderivedSurjective⟩ :=
    central_extension_nonabelian_simple_derived_quasisimple restrictedMap
      hrestrictedSurjective hrestrictedCentral hnonab
  let derivedGroup := commutator preimageGroup
  let liftedGroup := Subgroup.map preimageGroup.subtype derivedGroup
  let : derivedGroup.Characteristic := by
    dsimp only [derivedGroup]
    rw [commutator_def]
    infer_instance
  have hliftedNormal : liftedGroup.Normal := by infer_instance
  let derivedEquiv := derivedGroup.equivMapOfInjective preimageGroup.subtype
    preimageGroup.subtype_injective
  have hderivedKernel : (restrictedMap.comp derivedGroup.subtype).ker ≤
      Subgroup.center derivedGroup := by
    intro element helement
    apply Subgroup.mem_center_iff.mpr
    intro other
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hrestrictedCentral helement) other.val
  have hcenter := surjective_centerless_image_center_eq_kernel
    (restrictedMap.comp derivedGroup.subtype) hderivedSurjective hderivedKernel
    (nonabelian_simple_center_eq_bot hnonab)
  let quotientEquiv := (QuotientGroup.quotientMulEquivOfEq hcenter).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (restrictedMap.comp derivedGroup.subtype) hderivedSurjective)
  exact ⟨liftedGroup, hliftedNormal, quasisimple_of_mulEquiv derivedEquiv hderivedQuasisimple,
    ⟨(centerQuotientEquiv derivedEquiv).symm.trans quotientEquiv⟩⟩

theorem central_extension_minimal_normal_simple_factor_has_component_lift
    {G Image : Type*} [Group G] [Group Image]
    (homomorphism : G →* Image) (hsurjective : Function.Surjective homomorphism)
    (hcentral : homomorphism.ker ≤ Subgroup.center G)
    (minimalGroup : Subgroup Image) (hminimalNormal : minimalGroup.Normal)
    (simpleFactor : Subgroup minimalGroup) (hnormal : simpleFactor.Normal)
    (hsimple : IsSimpleGroup simpleFactor)
    (hnonab : ∃ first second : simpleFactor, first * second ≠ second * first) :
    ∃ component : Subgroup G, IsComponentOf component ⊤ ∧
      Nonempty ((component ⧸ Subgroup.center component) ≃* simpleFactor) := by
  let : minimalGroup.Normal := hminimalNormal
  let preimageGroup := Subgroup.comap homomorphism minimalGroup
  have hpreimageNormal : preimageGroup.Normal := hminimalNormal.comap homomorphism
  let restrictedMap : preimageGroup →* minimalGroup :=
    (homomorphism.comp preimageGroup.subtype).codRestrict minimalGroup
      (fun element => element.property)
  have hrestrictedSurjective : Function.Surjective restrictedMap := by
    intro element
    obtain ⟨preimage, hpreimage⟩ := hsurjective element.val
    have hmem : preimage ∈ preimageGroup := by
      change homomorphism preimage ∈ minimalGroup
      rw [hpreimage]
      exact element.property
    exact ⟨⟨preimage, hmem⟩, Subtype.ext hpreimage⟩
  have hrestrictedCentral : restrictedMap.ker ≤ Subgroup.center preimageGroup := by
    intro element helement
    have hkernel : element.val ∈ homomorphism.ker := by
      change homomorphism element.val = 1
      exact congrArg Subtype.val helement
    apply Subgroup.mem_center_iff.mpr
    intro other
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hcentral hkernel) other.val
  obtain ⟨liftedGroup, hliftedNormal, hliftedQuasisimple, ⟨quotientEquiv⟩⟩ :=
    central_extension_normal_simple_factor_has_normal_quasisimple_lift restrictedMap
      hrestrictedSurjective hrestrictedCentral simpleFactor hnormal hsimple hnonab
  let component := Subgroup.map preimageGroup.subtype liftedGroup
  let liftEquiv := liftedGroup.equivMapOfInjective preimageGroup.subtype
    preimageGroup.subtype_injective
  exact ⟨component, normal_quasisimple_internal_subgroup_maps_to_component
    preimageGroup hpreimageNormal liftedGroup hliftedNormal hliftedQuasisimple,
    ⟨(centerQuotientEquiv liftEquiv).symm.trans quotientEquiv⟩⟩

end CFSG.RankThreeCoreUniqueness.Helpers
