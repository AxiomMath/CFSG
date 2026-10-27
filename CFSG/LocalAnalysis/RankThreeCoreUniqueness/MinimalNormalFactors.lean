module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoreConjugacy

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem minimal_normal_map_automorphism
    {G : Type*} [Group G] (subgroup : Subgroup G)
    (hminimal : Minimal (fun normalGroup => normalGroup.Normal ∧ normalGroup ≠ ⊥) subgroup)
    (automorphism : MulAut G) :
    Minimal (fun normalGroup => normalGroup.Normal ∧ normalGroup ≠ ⊥)
      (Subgroup.map automorphism.toMonoidHom subgroup) := by
  refine ⟨⟨hminimal.prop.1.map automorphism.toMonoidHom automorphism.surjective,
    ?_⟩, ?_⟩
  · exact ((Subgroup.map_eq_bot_iff_of_injective subgroup automorphism.injective).not).mpr
      hminimal.prop.2
  · intro smaller hsmaller hsmallerLe
    have hinverseLe := Subgroup.map_mono (f := automorphism.symm.toMonoidHom) hsmallerLe
    rw [map_automorphism_symm_map] at hinverseLe
    have hinverseNormal := hsmaller.1.map automorphism.symm.toMonoidHom automorphism.symm.surjective
    have hinverseNontrivial : smaller.map automorphism.symm.toMonoidHom ≠ ⊥ :=
      ((Subgroup.map_eq_bot_iff_of_injective smaller automorphism.symm.injective).not).mpr hsmaller.2
    have hequal := hminimal.eq_of_le ⟨hinverseNormal, hinverseNontrivial⟩ hinverseLe
    have hmapped := congrArg (Subgroup.map automorphism.toMonoidHom) hequal
    have hcancel : automorphism.toMonoidHom.comp automorphism.symm.toMonoidHom = MonoidHom.id G := by
      ext element
      exact automorphism.apply_symm_apply element
    rw [Subgroup.map_map, hcancel, Subgroup.map_id] at hmapped
    exact hmapped.symm.le

theorem distinct_minimal_normal_subgroups_disjoint
    {G : Type*} [Group G] (first second : Subgroup G)
    (hfirst : Minimal (fun subgroup => subgroup.Normal ∧ subgroup ≠ ⊥) first)
    (hsecond : Minimal (fun subgroup => subgroup.Normal ∧ subgroup ≠ ⊥) second)
    (hdistinct : first ≠ second) : Disjoint first second := by
  let : first.Normal := hfirst.prop.1
  let : second.Normal := hsecond.prop.1
  apply disjoint_iff.mpr
  by_contra hnontrivial
  have hfirstEq := hfirst.eq_of_le ⟨by infer_instance, hnontrivial⟩ inf_le_left
  have hsecondEq := hsecond.eq_of_le ⟨by infer_instance, hnontrivial⟩ inf_le_right
  exact hdistinct (hfirstEq.symm.trans hsecondEq)

theorem automorphism_orbit_join_characteristic
    {G : Type*} [Group G] (subgroup : Subgroup G) :
    (⨆ automorphism : MulAut G, Subgroup.map automorphism.toMonoidHom subgroup).Characteristic := by
  apply Subgroup.characteristic_iff_map_le.mpr
  intro outerAutomorphism
  rw [Subgroup.map_iSup]
  apply iSup_le
  intro innerAutomorphism
  rw [Subgroup.map_map]
  exact le_iSup_of_le (innerAutomorphism.trans outerAutomorphism) le_rfl

theorem characteristically_simple_minimal_normal_isSimpleGroup
    {G : Type*} [Group G]
    (hcharacteristic : ∀ subgroup : Subgroup G, subgroup.Characteristic →
      subgroup = ⊥ ∨ subgroup = ⊤)
    (minimalGroup : Subgroup G)
    (hminimal : Minimal (fun subgroup => subgroup.Normal ∧ subgroup ≠ ⊥) minimalGroup) :
    IsSimpleGroup minimalGroup := by
  let orbitJoin := ⨆ automorphism : MulAut G, Subgroup.map automorphism.toMonoidHom minimalGroup
  have hbaseLe : minimalGroup ≤ orbitJoin := by
    have hbound := le_iSup (fun automorphism : MulAut G =>
      Subgroup.map automorphism.toMonoidHom minimalGroup) (MulEquiv.refl G)
    change Subgroup.map (MonoidHom.id G) minimalGroup ≤ orbitJoin at hbound
    simpa only [Subgroup.map_id] using hbound
  have horbitTop : orbitJoin = ⊤ := by
    rcases hcharacteristic orbitJoin (automorphism_orbit_join_characteristic minimalGroup) with
      hbottom | htop
    · exact False.elim (hminimal.prop.2 (le_bot_iff.mp (hbottom ▸ hbaseLe)))
    · exact htop
  have hdecomposition : minimalGroup ⊔ Subgroup.centralizer (minimalGroup : Set G) = ⊤ := by
    apply top_le_iff.mp
    rw [← horbitTop]
    apply iSup_le
    intro automorphism
    by_cases hequal : Subgroup.map automorphism.toMonoidHom minimalGroup = minimalGroup
    · rw [hequal]
      exact le_sup_left
    · let imageGroup := Subgroup.map automorphism.toMonoidHom minimalGroup
      have himageMinimal := minimal_normal_map_automorphism minimalGroup hminimal automorphism
      let : minimalGroup.Normal := hminimal.prop.1
      let : imageGroup.Normal := himageMinimal.prop.1
      have hdisjoint := distinct_minimal_normal_subgroups_disjoint imageGroup minimalGroup
        himageMinimal hminimal hequal
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (Subgroup.commutator_eq_bot_of_disjoint hdisjoint)).trans le_sup_right
  apply Subgroup.isSimpleGroup_iff.mpr
  refine ⟨hminimal.prop.2, ?_⟩
  intro smaller hsmallerLe hsmallerNormal
  have hnormalizer : (⊤ : Subgroup G) ≤ Subgroup.normalizer (smaller : Set G) := by
    rw [← hdecomposition]
    apply sup_le
    · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hsmallerLe).mp hsmallerNormal
    · exact (Subgroup.centralizer_le hsmallerLe).trans (Subgroup.centralizer_le_normalizer _)
  have hnormal : smaller.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hnormalizer)
  by_cases hbottom : smaller = ⊥
  · exact Or.inl hbottom
  · exact Or.inr (hminimal.eq_of_le ⟨hnormal, hbottom⟩ hsmallerLe)

theorem minimal_normal_subgroup_characteristically_simple
    {G : Type*} [Group G] (minimalGroup : Subgroup G)
    (hminimal : Minimal (fun subgroup => subgroup.Normal ∧ subgroup ≠ ⊥) minimalGroup) :
    ∀ subgroup : Subgroup minimalGroup, subgroup.Characteristic → subgroup = ⊥ ∨ subgroup = ⊤ := by
  let : minimalGroup.Normal := hminimal.prop.1
  intro subgroup hcharacteristic
  let : subgroup.Characteristic := hcharacteristic
  have hmappedNormal : (Subgroup.map minimalGroup.subtype subgroup).Normal := by infer_instance
  by_cases hbottom : subgroup = ⊥
  · exact Or.inl hbottom
  · right
    have hmappedNontrivial : Subgroup.map minimalGroup.subtype subgroup ≠ ⊥ :=
      ((Subgroup.map_eq_bot_iff_of_injective subgroup minimalGroup.subtype_injective).not).mpr hbottom
    have hequal := hminimal.eq_of_le ⟨hmappedNormal, hmappedNontrivial⟩ (Subgroup.map_subtype_le _)
    apply top_le_iff.mp
    intro element _helement
    have himage : element.val ∈ Subgroup.map minimalGroup.subtype subgroup := by
      rw [hequal]
      exact element.property
    obtain ⟨preimage, hpreimage, hequalElement⟩ := himage
    exact (Subtype.ext hequalElement : preimage = element) ▸ hpreimage

theorem finite_minimal_normal_perfect_has_simple_normal_factor
    {G : Type*} [Group G] [Finite G] (minimalGroup : Subgroup G)
    (hminimal : Minimal (fun subgroup => subgroup.Normal ∧ subgroup ≠ ⊥) minimalGroup)
    (hperfect : Group.IsPerfect minimalGroup) :
    ∃ simpleFactor : Subgroup minimalGroup, simpleFactor.Normal ∧ IsSimpleGroup simpleFactor ∧
      (∃ first second : simpleFactor, first * second ≠ second * first) := by
  classical
  let : Nontrivial minimalGroup := minimalGroup.nontrivial_iff_ne_bot.mpr hminimal.prop.2
  obtain ⟨simpleFactor, _, hfactorMinimal⟩ := Finite.exists_le_minimal
    (p := fun subgroup : Subgroup minimalGroup => subgroup.Normal ∧ subgroup ≠ ⊥)
    (a := ⊤) ⟨by infer_instance, top_ne_bot⟩
  have hcharacteristic := minimal_normal_subgroup_characteristically_simple minimalGroup hminimal
  have hsimple := characteristically_simple_minimal_normal_isSimpleGroup
    hcharacteristic simpleFactor hfactorMinimal
  have hnonabelian : ¬ IsMulCommutative simpleFactor := by
    intro hcommutative
    let orbitJoin := ⨆ automorphism : MulAut minimalGroup,
      Subgroup.map automorphism.toMonoidHom simpleFactor
    have horbitTop : orbitJoin = ⊤ := by
      rcases hcharacteristic orbitJoin (automorphism_orbit_join_characteristic simpleFactor) with
        hbottom | htop
      · have hbound := le_iSup (fun automorphism : MulAut minimalGroup =>
          Subgroup.map automorphism.toMonoidHom simpleFactor) (MulEquiv.refl minimalGroup)
        have hbaseLe : simpleFactor ≤ orbitJoin := by
          change Subgroup.map (MonoidHom.id minimalGroup) simpleFactor ≤ orbitJoin at hbound
          simpa only [Subgroup.map_id] using hbound
        exact False.elim (hfactorMinimal.prop.2 (le_bot_iff.mp (hbottom ▸ hbaseLe)))
      · exact htop
    have hcentralizer : orbitJoin ≤ Subgroup.centralizer (simpleFactor : Set minimalGroup) := by
      apply iSup_le
      intro automorphism
      by_cases hequal : Subgroup.map automorphism.toMonoidHom simpleFactor = simpleFactor
      · rw [hequal]
        exact Subgroup.le_centralizer_iff_isMulCommutative.mpr hcommutative
      · let imageGroup := Subgroup.map automorphism.toMonoidHom simpleFactor
        have himageMinimal := minimal_normal_map_automorphism simpleFactor hfactorMinimal automorphism
        let : simpleFactor.Normal := hfactorMinimal.prop.1
        let : imageGroup.Normal := himageMinimal.prop.1
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (Subgroup.commutator_eq_bot_of_disjoint
            (distinct_minimal_normal_subgroups_disjoint imageGroup simpleFactor
              himageMinimal hfactorMinimal hequal))
    rw [horbitTop] at hcentralizer
    have hcenterTop : Subgroup.center minimalGroup = ⊤ := by
      have hfactorCentral : simpleFactor ≤ Subgroup.center minimalGroup := by
        intro element helement
        apply Subgroup.mem_center_iff.mpr
        intro other
        exact (Subgroup.mem_centralizer_iff.mp (hcentralizer (Subgroup.mem_top other))
          element helement).symm
      rcases hcharacteristic (Subgroup.center minimalGroup) (by infer_instance) with hbottom | htop
      · exact False.elim (hfactorMinimal.prop.2 (le_bot_iff.mp (hbottom ▸ hfactorCentral)))
      · exact htop
    let : Group.IsPerfect minimalGroup := hperfect
    apply Group.IsPerfect.not_isMulCommutative minimalGroup
    apply isMulCommutative_iff.mpr
    intro first second
    exact Subgroup.mem_center_iff.mp (hcenterTop ▸ Subgroup.mem_top second) first
  refine ⟨simpleFactor, hfactorMinimal.prop.1, hsimple, ?_⟩
  by_contra hnoPair
  push Not at hnoPair
  exact hnonabelian (isMulCommutative_iff.mpr hnoPair)

end CFSG.RankThreeCoreUniqueness.Helpers
