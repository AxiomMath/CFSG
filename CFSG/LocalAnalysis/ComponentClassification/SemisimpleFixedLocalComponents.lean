module

public import CFSG.LocalAnalysis.ComponentClassification.TwoComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionDiagonal
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionOrbitDecomposition

public section

open CFSG.Open

namespace CFSG.ComponentClassification.SemisimpleFixedLocalComponents

theorem lies_in_invariant_factor {G : Type*} [Group G] [Finite G]
    {Index : Type*} [Fintype Index]
    (factors : Index → Subgroup G) (hnormal : ∀ index, (factors index).Normal)
    (hcenter : ∀ index, Subgroup.center (factors index) = ⊥)
    (hsimple : ∀ index, IsSimpleGroup (factors index))
    (hperfect : ∀ index, Group.IsPerfect (factors index))
    (hcommutes : Pairwise (fun first second => ⁅factors first, factors second⁆ = ⊥))
    (hcover : (⨆ index, factors index) = ⊤)
    (permutation : Index → Index) (hpermutation : Function.Involutive permutation)
    (automorphism : MulAut G) (hinvolutive : Function.Involutive automorphism)
    (himages : ∀ index, (factors index).map automorphism.toMonoidHom = factors (permutation index))
    (localComponent : Subgroup (FixedCommutingProduct.fixedSubgroup automorphism))
    (hlocal : TwoComponents.IsTwoComponent localComponent)
    (hnotQuasisimple : ¬ IsQuasisimple localComponent) :
    ∃ index, permutation index = index ∧
      localComponent.map (FixedCommutingProduct.fixedSubgroup automorphism).subtype ≤ factors index := by
  classical
  let fixed := FixedCommutingProduct.fixedSubgroup automorphism
  let orbits := InvolutionOrbitDecomposition.orbitFactor factors permutation
  let fixedOrbits := InvolutionOrbitDecomposition.fixedOrbit factors permutation automorphism
  let localOrbits := fun index => (fixedOrbits index).subgroupOf fixed
  have horbitNormal : ∀ index, (orbits index).Normal := by
    intro index
    let : (factors index).Normal := hnormal index
    let : (factors (permutation index)).Normal := hnormal (permutation index)
    exact Subgroup.sup_normal _ _
  have hlocalNormal : ∀ index, (localOrbits index).Normal := by
    intro index
    let : (orbits index).Normal := horbitNormal index
    exact InvolutionDiagonal.fixed_factor_normal (orbits index) automorphism
  have horbitLe : ∀ index, fixedOrbits index ≤ fixed := fun _ => inf_le_right
  have hlocalMap : ∀ index, (localOrbits index).map fixed.subtype = fixedOrbits index :=
    fun index => Subgroup.map_subgroupOf_eq_of_le (horbitLe index)
  have hlocalCover : (⨆ index, localOrbits index) = ⊤ := by
    have htopMap : (⊤ : Subgroup fixed).map fixed.subtype = fixed := by
      ext member
      constructor
      · rintro ⟨lift, _, rfl⟩
        exact lift.property
      · intro hmember
        exact ⟨⟨member, hmember⟩, Subgroup.mem_top _, rfl⟩
    apply Subgroup.map_injective fixed.subtype_injective
    rw [Subgroup.map_iSup, htopMap]
    simp only [hlocalMap]
    have hdecomposition := InvolutionOrbitDecomposition.fixed_iSup factors hnormal hcenter
      hcommutes permutation hpermutation automorphism himages
    rw [hcover, top_inf_eq] at hdecomposition
    exact hdecomposition.symm
  obtain ⟨containing, ⟨index, rfl⟩, hcontained⟩ :=
    TwoComponentJoins.exists_le_of_le_sSup localComponent hlocal (Set.range localOrbits)
      (by
        rintro candidate ⟨index, rfl⟩
        exact Components.chain_of_mathlib_subnormal (hlocalNormal index).isSubnormal)
      (by rw [sSup_range, hlocalCover]; exact le_top)
  have hindexFixed : permutation index = index := by
    by_contra hne
    let : (factors index).Normal := hnormal index
    let : IsSimpleGroup (factors index) := hsimple index
    let : Group.IsPerfect (factors index) := hperfect index
    have hfactorDisjoint : Disjoint (factors index) (factors (permutation index)) :=
      CenterlessCommutingFamily.disjoint_of_centralizes _ _ (hcenter index)
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcommutes hne))
    have hfactorCommutes : ⁅factors index, (factors index).map automorphism.toMonoidHom⁆ = ⊥ := by
      rw [himages]
      exact hcommutes (Ne.symm hne)
    have hquasi : IsQuasisimple (fixedOrbits index) := by
      have hdiagonal := InvolutionDiagonal.fixed_quasisimple (factors index) automorphism
        hinvolutive hfactorCommutes (by rw [himages]; exact hfactorDisjoint)
      change IsQuasisimple ↥((factors index ⊔ (factors index).map automorphism.toMonoidHom) ⊓ fixed)
        at hdiagonal
      rw [himages] at hdiagonal
      exact hdiagonal
    have hlocalQuasi : IsQuasisimple (localOrbits index) := Components.quasisimple_of_equiv
      (Subgroup.subgroupOfEquivOfLe (horbitLe index)) hquasi
    let restricted := localComponent.subgroupOf (localOrbits index)
    have hrestricted := TwoComponentTransport.of_overgroup hlocal hcontained
    let : Group.IsPerfect restricted := ⟨TwoComponents.perfect hrestricted⟩
    have hnontrivial : restricted ≠ ⊥ :=
      restricted.nontrivial_iff_ne_bot.mp (TwoComponents.nontrivial hrestricted)
    have hrestrictedQuasi := Quasisimple.perfect_subnormal_quasisimple hlocalQuasi
      restricted hrestricted.1 hnontrivial
    exact hnotQuasisimple (Components.quasisimple_of_equiv
      (Subgroup.subgroupOfEquivOfLe hcontained).symm hrestrictedQuasi)
  refine ⟨index, hindexFixed, ?_⟩
  have hmap := Subgroup.map_mono (f := fixed.subtype) hcontained
  rw [hlocalMap] at hmap
  have horbitContained : fixedOrbits index ≤ factors index := by
    dsimp [fixedOrbits, InvolutionOrbitDecomposition.fixedOrbit,
      InvolutionOrbitDecomposition.orbitFactor]
    rw [hindexFixed, sup_idem]
    exact inf_le_left
  exact hmap.trans horbitContained

theorem simple_of_normalClosure_eq_top {G : Type*} [Group G] [Finite G]
    {Index : Type*} [Fintype Index]
    (factors : Index → Subgroup G) (hnormal : ∀ index, (factors index).Normal)
    (hcenter : ∀ index, Subgroup.center (factors index) = ⊥)
    (hsimple : ∀ index, IsSimpleGroup (factors index))
    (hperfect : ∀ index, Group.IsPerfect (factors index))
    (hcommutes : Pairwise (fun first second => ⁅factors first, factors second⁆ = ⊥))
    (hcover : (⨆ index, factors index) = ⊤)
    (permutation : Index → Index) (hpermutation : Function.Involutive permutation)
    (automorphism : MulAut G) (hinvolutive : Function.Involutive automorphism)
    (himages : ∀ index, (factors index).map automorphism.toMonoidHom = factors (permutation index))
    (localComponent : Subgroup (FixedCommutingProduct.fixedSubgroup automorphism))
    (hlocal : TwoComponents.IsTwoComponent localComponent)
    (hnotQuasisimple : ¬ IsQuasisimple localComponent)
    (hclosure : Subgroup.normalClosure
      (localComponent.map (FixedCommutingProduct.fixedSubgroup automorphism).subtype : Set G) = ⊤) :
    IsSimpleGroup G := by
  obtain ⟨index, _, hcontained⟩ := lies_in_invariant_factor factors hnormal hcenter hsimple hperfect
    hcommutes hcover permutation hpermutation automorphism hinvolutive himages
      localComponent hlocal hnotQuasisimple
  let : (factors index).Normal := hnormal index
  let : IsSimpleGroup (factors index) := hsimple index
  have htop : factors index = ⊤ := by
    apply top_unique
    rw [← hclosure]
    exact Subgroup.normalClosure_le_normal hcontained
  exact ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).symm.isSimpleGroup

theorem normalClosure_simple_extension {G : Type*} [Group G] [Finite G]
    (normalSubgroup : Subgroup G) [normalSubgroup.Normal] (element : G)
    {Index : Type*} [Fintype Index]
    (factors : Index → Subgroup normalSubgroup) (hnormal : ∀ index, (factors index).Normal)
    (hcenter : ∀ index, Subgroup.center (factors index) = ⊥)
    (hsimple : ∀ index, IsSimpleGroup (factors index))
    (hperfect : ∀ index, Group.IsPerfect (factors index))
    (hcommutes : Pairwise (fun first second => ⁅factors first, factors second⁆ = ⊥))
    (hcover : (⨆ index, factors index) = ⊤)
    (permutation : Index → Index) (hpermutation : Function.Involutive permutation)
    (hinvolutive : Function.Involutive (MulAut.conjNormal (H := normalSubgroup) element))
    (himages : ∀ index, (factors index).map
      (MulAut.conjNormal (H := normalSubgroup) element).toMonoidHom = factors (permutation index))
    (localComponent : Subgroup
      (FixedCommutingProduct.fixedSubgroup (MulAut.conjNormal (H := normalSubgroup) element)))
    (hlocal : TwoComponents.IsTwoComponent localComponent)
    (hnotQuasisimple : ¬ IsQuasisimple localComponent)
    (hclosure : Subgroup.normalClosure
      ((localComponent.map (FixedCommutingProduct.fixedSubgroup
        (MulAut.conjNormal (H := normalSubgroup) element)).subtype).map normalSubgroup.subtype : Set G) =
          normalSubgroup)
    (hambientCover : normalSubgroup ⊔ Subgroup.zpowers element = ⊤) :
    IsSimpleGroup normalSubgroup := by
  let automorphism := MulAut.conjNormal (H := normalSubgroup) element
  obtain ⟨index, hindexFixed, hcontained⟩ := lies_in_invariant_factor factors hnormal hcenter hsimple
    hperfect hcommutes hcover permutation hpermutation automorphism hinvolutive himages
      localComponent hlocal hnotQuasisimple
  let factor := factors index
  let image := factor.map normalSubgroup.subtype
  have himageLe : image ≤ normalSubgroup := Subgroup.map_subtype_le _
  have hnormalizes : normalSubgroup ≤ Subgroup.normalizer (image : Set G) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro actor hactor member hmember
    obtain ⟨lift, hlift, rfl⟩ := Subgroup.mem_map.mp hmember
    exact Subgroup.mem_map_of_mem normalSubgroup.subtype
      ((hnormal index).conj_mem lift hlift (⟨actor, hactor⟩ : normalSubgroup))
  have helementNormalizes : element ∈ Subgroup.normalizer (image : Set G) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    have hinvariant : factor.map automorphism.toMonoidHom = factor := by
      change (factors index).map automorphism.toMonoidHom = factors index
      rw [himages, hindexFixed]
    have hequivariance : (MulAut.conj element).toMonoidHom.comp normalSubgroup.subtype =
        normalSubgroup.subtype.comp automorphism.toMonoidHom := by
      ext member
      exact (MulAut.conjNormal_apply element member).symm
    change (factor.map normalSubgroup.subtype).map (MulAut.conj element).toMonoidHom =
      factor.map normalSubgroup.subtype
    rw [Subgroup.map_map, hequivariance, ← Subgroup.map_map, hinvariant]
  let : image.Normal := Subgroup.normalizer_eq_top_iff.mp (top_unique (by
    rw [← hambientCover]
    exact sup_le hnormalizes (Subgroup.zpowers_le.mpr helementNormalizes)))
  have hnormalEq : normalSubgroup = image := by
    apply le_antisymm _ himageLe
    rw [← hclosure]
    exact Subgroup.normalClosure_le_normal (Subgroup.map_mono hcontained)
  let : IsSimpleGroup factor := hsimple index
  let equivalence := factor.equivMapOfInjective normalSubgroup.subtype normalSubgroup.subtype_injective
  let : IsSimpleGroup image := equivalence.symm.isSimpleGroup
  exact (MulEquiv.subgroupCongr hnormalEq).isSimpleGroup

end CFSG.ComponentClassification.SemisimpleFixedLocalComponents
