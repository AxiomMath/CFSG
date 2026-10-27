module

public import CFSG.Foundations.KCoreOpen

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem finite_nonsolvable_has_characteristic_perfect_subgroup
    {G : Type*} [Group G] [Finite G] (hnonsolvable : ¬ Group.IsSolvable G) :
    ∃ perfectGroup : Subgroup G, perfectGroup.Characteristic ∧ perfectGroup ≠ ⊥ ∧
      Group.IsPerfect perfectGroup := by
  classical
  obtain ⟨perfectGroup, hminimal⟩ := (Set.toFinite (Set.range (derivedSeries G))).exists_minimal
    ⟨derivedSeries G 0, ⟨0, rfl⟩⟩
  obtain ⟨index, rfl⟩ := hminimal.prop
  have hnext : derivedSeries G (index + 1) = derivedSeries G index :=
    hminimal.eq_of_le ⟨index + 1, rfl⟩
      (derivedSeries_antitone G (Nat.le_succ index))
  refine ⟨derivedSeries G index, by infer_instance, ?_, ?_⟩
  · intro hzero
    exact hnonsolvable ⟨index, hzero⟩
  · apply Subgroup.isPerfect_iff.mpr
    rwa [derivedSeries_succ] at hnext

theorem perfect_group_has_nonabelian_simple_quotient
    {G : Type*} [Group G] [Finite G] [Nontrivial G] [Group.IsPerfect G] :
    ∃ normalGroup : Subgroup G, ∃ hnormal : normalGroup.Normal, letI := hnormal;
      IsSimpleGroup (G ⧸ normalGroup) ∧
      (∃ first second : G ⧸ normalGroup, first * second ≠ second * first) := by
  classical
  obtain ⟨normalGroup, _, hmaximal⟩ := Finite.exists_le_maximal
    (p := fun subgroup : Subgroup G => subgroup.Normal ∧ subgroup ≠ ⊤)
    (a := ⊥) ⟨by infer_instance, bot_ne_top⟩
  let : normalGroup.Normal := hmaximal.prop.1
  let : Nontrivial (G ⧸ normalGroup) := QuotientGroup.nontrivial_iff.mpr hmaximal.prop.2
  have hsimple : IsSimpleGroup (G ⧸ normalGroup) := by
    constructor
    intro subgroup hnormal
    by_cases htop : subgroup = ⊤
    · exact Or.inr htop
    · left
      let homomorphism := QuotientGroup.mk' normalGroup
      have hpreimageNormal : (Subgroup.comap homomorphism subgroup).Normal :=
        hnormal.comap homomorphism
      have hpreimageProper : Subgroup.comap homomorphism subgroup ≠ ⊤ := by
        intro hequal
        have hmapped := congrArg (Subgroup.map homomorphism) hequal
        rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
          ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr
            (QuotientGroup.mk'_surjective _)] at hmapped
        exact htop hmapped
      have hkernelLe : normalGroup ≤ Subgroup.comap homomorphism subgroup := by
        simpa only [homomorphism, QuotientGroup.ker_mk'] using
          (Subgroup.ker_le_comap homomorphism subgroup)
      have hequal := hmaximal.eq_of_le ⟨hpreimageNormal, hpreimageProper⟩ hkernelLe
      have hmapped := congrArg (Subgroup.map homomorphism) hequal
      rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at hmapped
      have hkernelMap : Subgroup.map homomorphism normalGroup = ⊥ := by
        apply (Subgroup.map_eq_bot_iff normalGroup).mpr
        simp only [homomorphism, QuotientGroup.ker_mk', le_rfl]
      exact hmapped.symm.trans hkernelMap
  refine ⟨normalGroup, hmaximal.prop.1, hsimple, ?_⟩
  by_contra hnonab
  have hcommutative : IsMulCommutative (G ⧸ normalGroup) := by
    apply isMulCommutative_iff.mpr
    push Not at hnonab
    exact hnonab
  exact Group.IsPerfect.not_isMulCommutative (G ⧸ normalGroup) hcommutative

theorem kProper_simple_quotient_order
    {G : Type*} [Group G] (hK : IsKProperByOrder G)
    (sectionGroup : Subgroup G) (hproper : sectionGroup ≠ ⊤)
    (kernelGroup : Subgroup sectionGroup) (hnormal : kernelGroup.Normal)
    (hsimple : IsSimpleGroup (sectionGroup ⧸ kernelGroup))
    (hnonab : ∃ first second : sectionGroup ⧸ kernelGroup,
      first * second ≠ second * first) :
    Nat.card (sectionGroup ⧸ kernelGroup) ∈ knownSimpleOrders :=
  CFSG.KCore.KProperNonab.catalogue_of_surjective_transfer knownSimpleOrders_isoTransfer hK
    sectionGroup hproper hnonab (QuotientGroup.mk' kernelGroup) (QuotientGroup.mk'_surjective _)

theorem kProper_nonsolvable_overgroup_has_simple_section
    {G : Type*} [Group G] [Finite G] (hK : IsKProperByOrder G)
    (overgroup : Subgroup G) (hproper : overgroup ≠ ⊤)
    (hnonsolvable : ¬ Group.IsSolvable overgroup) :
    ∃ sectionGroup : Subgroup G, sectionGroup ≤ overgroup ∧
      Group.IsPerfect sectionGroup ∧
      ∃ kernelGroup : Subgroup sectionGroup, ∃ hnormal : kernelGroup.Normal, letI := hnormal;
        IsSimpleGroup (sectionGroup ⧸ kernelGroup) ∧
        (∃ first second : sectionGroup ⧸ kernelGroup, first * second ≠ second * first) ∧
        Nat.card (sectionGroup ⧸ kernelGroup) ∈ knownSimpleOrders := by
  obtain ⟨perfectInternal, _hcharacteristic, hnontrivial, hperfect⟩ :=
    finite_nonsolvable_has_characteristic_perfect_subgroup hnonsolvable
  let sectionGroup := Subgroup.map overgroup.subtype perfectInternal
  have hequiv : perfectInternal ≃* sectionGroup :=
    perfectInternal.equivMapOfInjective overgroup.subtype overgroup.subtype_injective
  have hsectionLe : sectionGroup ≤ overgroup := Subgroup.map_subtype_le _
  have hsectionProper : sectionGroup ≠ ⊤ := by
    intro htop
    exact hproper (top_le_iff.mp (htop ▸ hsectionLe))
  let : Nontrivial perfectInternal := (perfectInternal.nontrivial_iff_ne_bot).mpr hnontrivial
  let : Nontrivial sectionGroup := hequiv.injective.nontrivial
  let : Group.IsPerfect perfectInternal := hperfect
  have hsectionPerfect : Group.IsPerfect sectionGroup := by
    apply Subgroup.isPerfect_iff.mpr
    dsimp only [sectionGroup]
    rw [← Subgroup.map_commutator, Subgroup.commutator_eq_self]
  let : Group.IsPerfect sectionGroup := hsectionPerfect
  obtain ⟨kernelGroup, hnormal, hsimple, hnonab⟩ :=
    perfect_group_has_nonabelian_simple_quotient (G := sectionGroup)
  refine ⟨sectionGroup, hsectionLe, hsectionPerfect, kernelGroup, hnormal, hsimple, hnonab, ?_⟩
  exact kProper_simple_quotient_order hK sectionGroup hsectionProper kernelGroup hnormal
    hsimple hnonab

end CFSG.RankThreeCoreUniqueness.Helpers
