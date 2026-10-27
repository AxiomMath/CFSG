module

public import CFSG.CharacterTheory.TwoRankLowerBound.PrincipalBlockDefect

public section

open scoped Classical Pointwise

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] def classDefectAt {group : Type*} [Group group] (prime : ℕ)
    (primary : Subgroup group) (element : group) : Prop :=
  primary ≤ Subgroup.centralizer ({element} : Set group) ∧
    subgroupIsSylow prime (primary.subgroupOf (Subgroup.centralizer ({element} : Set group)))

theorem classDefectAt_classDefect {group : Type*} [Group group]
    {prime : ℕ} {primary : Subgroup group} {element : group}
    (hdefect : classDefectAt prime primary element) : classDefect prime (ConjClasses.mk element) primary := by
  obtain ⟨hcontains, sylow, hsylow⟩ := hdefect
  refine ⟨element, rfl, sylow, ?_⟩
  rw [hsylow]
  exact (Subgroup.map_subgroupOf_eq_of_le hcontains).symm

theorem classDefectAt_of_sylow_image {group : Type*} [Group group]
    (prime : ℕ) (element : group) (sylow : Sylow prime (Subgroup.centralizer ({element} : Set group))) :
    classDefectAt prime ((sylow : Subgroup _).map (Subgroup.centralizer ({element} : Set group)).subtype)
      element := by
  refine ⟨sylow_image_le _ sylow, sylow, ?_⟩
  change (sylow : Subgroup _) = ((sylow : Subgroup _).map
    (Subgroup.centralizer ({element} : Set group)).subtype).comap
      (Subgroup.centralizer ({element} : Set group)).subtype
  exact (Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _).symm

theorem classDefect_iff_exists_at {group : Type*} [Group group]
    (prime : ℕ) (conjugacyClass : ConjClasses group) (primary : Subgroup group) :
    classDefect prime conjugacyClass primary ↔
      ∃ element, ConjClasses.mk element = conjugacyClass ∧ classDefectAt prime primary element := by
  constructor
  · rintro ⟨element, hclass, sylow, rfl⟩
    exact ⟨element, hclass, classDefectAt_of_sylow_image prime element sylow⟩
  · rintro ⟨element, hclass, hdefect⟩
    rw [← hclass]
    exact classDefectAt_classDefect hdefect

set_option backward.isDefEq.respectTransparency false in
theorem conjugation_centralizer_singleton_eq {group : Type*} [Group group]
    (element conjugator : group) :
    (Subgroup.centralizer ({element} : Set group)).map (MulAut.conj conjugator).toMonoidHom =
      Subgroup.centralizer ({conjugator * element * conjugator⁻¹} : Set group) := by
  apply le_antisymm (conjugation_centralizer_singleton_le element conjugator)
  intro other hother
  have hbackward := conjugation_centralizer_singleton_le
    (conjugator * element * conjugator⁻¹) conjugator⁻¹
  have hconjugated := hbackward (Subgroup.mem_map_of_mem (MulAut.conj conjugator⁻¹).toMonoidHom hother)
  have hmember : conjugator⁻¹ * other * conjugator ∈ Subgroup.centralizer ({element} : Set group) := by
    change conjugator⁻¹ * other * conjugator⁻¹⁻¹ ∈
      Subgroup.centralizer ({conjugator⁻¹ * (conjugator * element * conjugator⁻¹) * conjugator⁻¹⁻¹} : Set group)
      at hconjugated
    have hequal : conjugator⁻¹ * (conjugator * element * conjugator⁻¹) * conjugator⁻¹⁻¹ = element := by group
    rw [hequal] at hconjugated
    simpa only [inv_inv] using hconjugated
  exact Subgroup.mem_map.mpr ⟨conjugator⁻¹ * other * conjugator, hmember, by
    change conjugator * (conjugator⁻¹ * other * conjugator) * conjugator⁻¹ = other
    group⟩

@[expose] noncomputable def centralizerConjugationEquiv {group : Type*} [Group group]
    (element conjugator : group) :
    Subgroup.centralizer ({element} : Set group) ≃*
      Subgroup.centralizer ({conjugator * element * conjugator⁻¹} : Set group) :=
  ((MulAut.conj conjugator).subgroupMap (Subgroup.centralizer ({element} : Set group))).trans
    (MulEquiv.subgroupCongr (conjugation_centralizer_singleton_eq element conjugator))

theorem centralizerConjugationEquiv_apply {group : Type*} [Group group]
    (element conjugator : group) (member : Subgroup.centralizer ({element} : Set group)) :
    (centralizerConjugationEquiv element conjugator member).val =
      conjugator * member.val * conjugator⁻¹ := rfl

set_option backward.isDefEq.respectTransparency false in
theorem classDefectAt_conjugation {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] {primary : Subgroup group} {element : group}
    (hdefect : classDefectAt prime primary element) (conjugator : group) :
    classDefectAt prime (primary.map (MulAut.conj conjugator).toMonoidHom)
      (conjugator * element * conjugator⁻¹) := by
  obtain ⟨hcontains, sylow, hsylow⟩ := hdefect
  have hprimary : primary = (sylow : Subgroup _).map
      (Subgroup.centralizer ({element} : Set group)).subtype := by
    rw [hsylow]
    exact (Subgroup.map_subgroupOf_eq_of_le hcontains).symm
  let equivalence := centralizerConjugationEquiv element conjugator
  let imageSylow := sylow.mapSurjective (f := equivalence.toMonoidHom) equivalence.surjective
  have himage : (primary.map (MulAut.conj conjugator).toMonoidHom) =
      (imageSylow : Subgroup _).map
        (Subgroup.centralizer ({conjugator * element * conjugator⁻¹} : Set group)).subtype := by
    change primary.map (MulAut.conj conjugator).toMonoidHom =
      (sylow.mapSurjective (f := equivalence.toMonoidHom) equivalence.surjective :
        Subgroup (Subgroup.centralizer ({conjugator * element * conjugator⁻¹} : Set group))).map _
    rw [hprimary, Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
    congr 1
  rw [himage]
  exact classDefectAt_of_sylow_image prime _ imageSylow

theorem classDefectAt_isPGroup {group : Type*} [Group group]
    {prime : ℕ} {primary : Subgroup group} {element : group}
    (hdefect : classDefectAt prime primary element) : IsPGroup prime primary :=
  classDefect_isPGroup (classDefectAt_classDefect hdefect)

theorem p_group_sylow_in_normalizer_is_sylow {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] (primary : Subgroup group) (hprimary : IsPGroup prime primary)
    (hmaximal : ∀ larger : Subgroup group, IsPGroup prime larger →
      primary ≤ larger → larger ≤ Subgroup.normalizer (primary : Set group) → larger = primary) :
    subgroupIsSylow prime primary := by
  obtain ⟨sylow, hcontains⟩ := hprimary.exists_le_sylow
  let localPrimary := primary.subgroupOf (sylow : Subgroup group)
  let localNormalizer := Subgroup.normalizer (localPrimary : Set (sylow : Subgroup group))
  have hnormalizer : localNormalizer.map (sylow : Subgroup group).subtype = primary := by
    apply hmaximal
    · exact (sylow.isPGroup'.to_subgroup localNormalizer).map _
    · rw [← Subgroup.map_subgroupOf_eq_of_le hcontains]
      exact Subgroup.map_mono Subgroup.le_normalizer
    · change (Subgroup.normalizer (primary.subgroupOf (sylow : Subgroup group) :
        Set (sylow : Subgroup group))).map (sylow : Subgroup group).subtype ≤ _
      rw [← Subgroup.subgroupOf_normalizer_eq hcontains]
      exact (Subgroup.subgroupOf_map_subtype _ _).le.trans inf_le_left
  have hequal : localNormalizer = localPrimary := by
    apply Subgroup.map_injective (Subgroup.subtype_injective (sylow : Subgroup group))
    rw [hnormalizer, Subgroup.map_subgroupOf_eq_of_le hcontains]
  let : Group.IsNilpotent (sylow : Subgroup group) := sylow.isPGroup'.isNilpotent
  have htop : localPrimary = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp
      Group.normalizerCondition_of_isNilpotent) localPrimary hequal
  refine ⟨sylow, ?_⟩
  apply le_antisymm
  · intro member hmember
    have hlocal : (⟨member, hmember⟩ : (sylow : Subgroup group)) ∈ localPrimary := by
      rw [htop]
      trivial
    exact hlocal
  · exact hcontains

theorem subgroupIsSylow_of_normalizer_control {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] (primary intermediate : Subgroup group)
    (hprimary : IsPGroup prime primary) (hcontains : primary ≤ intermediate)
    (hsylow : subgroupIsSylow prime (primary.subgroupOf intermediate))
    (hnormalizer : Subgroup.normalizer (primary : Set group) ≤ intermediate) :
    subgroupIsSylow prime primary := by
  obtain ⟨localSylow, hlocalSylow⟩ := hsylow
  apply p_group_sylow_in_normalizer_is_sylow prime primary hprimary
  intro larger hlarger hcontainsPrimary hnormalizes
  have hcontainsLarger : larger ≤ intermediate := hnormalizes.trans hnormalizer
  have hlocalContains : (localSylow : Subgroup intermediate) ≤ larger.subgroupOf intermediate := by
    rw [hlocalSylow]
    exact Subgroup.comap_mono hcontainsPrimary
  have hequal := localSylow.is_maximal' hlarger.comap_subtype hlocalContains
  rw [hlocalSylow] at hequal
  have himage := congrArg (Subgroup.map intermediate.subtype) hequal
  change (larger.subgroupOf intermediate).map intermediate.subtype =
    (primary.subgroupOf intermediate).map intermediate.subtype at himage
  rwa [Subgroup.map_subgroupOf_eq_of_le hcontainsLarger,
    Subgroup.map_subgroupOf_eq_of_le hcontains] at himage

theorem classDefectAt_subgroup {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] (intermediate primary : Subgroup group)
    (hcontains : primary ≤ intermediate) (element : intermediate)
    (hdefect : classDefectAt prime primary element.val) :
    classDefectAt prime (primary.subgroupOf intermediate) element := by
  obtain ⟨hcentralizes, sylow, hsylow⟩ := hdefect
  have hlocalCentralizes : primary.subgroupOf intermediate ≤
      Subgroup.centralizer ({element} : Set intermediate) := by
    intro member hmember
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcentralizes hmember)
  refine ⟨hlocalCentralizes, ?_⟩
  let localCentralizer := Subgroup.centralizer ({element} : Set intermediate)
  let ambientCentralizer := Subgroup.centralizer ({element.val} : Set group)
  let inclusion : localCentralizer →* ambientCentralizer :=
    { toFun member := ⟨member.val.val, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp member.property))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hinjective : Function.Injective inclusion := by
    intro left right hequal
    exact Subtype.ext (Subtype.ext (congrArg (fun member => member.val) hequal))
  have hrange : (sylow : Subgroup ambientCentralizer) ≤ inclusion.range := by
    intro member hmember
    have hprimary : member.val ∈ primary := by
      rw [hsylow] at hmember
      exact hmember
    let localMember : intermediate := ⟨member.val, hcontains hprimary⟩
    have hcentral : localMember ∈ localCentralizer := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp member.property
    exact ⟨⟨localMember, hcentral⟩, rfl⟩
  refine ⟨sylow.comapOfInjective inclusion hinjective hrange, ?_⟩
  change (sylow.comapOfInjective inclusion hinjective hrange : Subgroup localCentralizer) = _
  rw [Sylow.coe_comapOfInjective, hsylow]
  rfl

theorem classDefectAt_normalizer_lift {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] (primary : Subgroup group)
    (element : Subgroup.normalizer (primary : Set group))
    (hlocal : classDefectAt prime
      (primary.subgroupOf (Subgroup.normalizer (primary : Set group))) element) :
    classDefectAt prime primary element.val := by
  let normalizer := Subgroup.normalizer (primary : Set group)
  let centralizer := Subgroup.centralizer ({element.val} : Set group)
  have hcontains : primary ≤ centralizer := by
    intro member hmember
    have hlocalMember : (⟨member, Subgroup.le_normalizer hmember⟩ : normalizer) ∈
        Subgroup.centralizer ({element} : Set normalizer) := hlocal.1 hmember
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hlocalMember))
  have hprimary : IsPGroup prime primary := by
    have hgroup := (classDefectAt_isPGroup hlocal).map normalizer.subtype
    rwa [Subgroup.map_subgroupOf_eq_of_le Subgroup.le_normalizer] at hgroup
  obtain ⟨localSylow, hlocalSylow⟩ := hlocal.2
  refine ⟨hcontains, p_group_sylow_in_normalizer_is_sylow prime _ hprimary.comap_subtype ?_⟩
  intro larger hlarger hcontainsPrimary hnormalizes
  let ambientLarger := larger.map centralizer.subtype
  have hcontainsAmbient : ambientLarger ≤ normalizer := by
    have hmap := (Subgroup.map_mono hnormalizes).trans
      (Subgroup.le_normalizer_map centralizer.subtype)
    rw [Subgroup.map_subgroupOf_eq_of_le hcontains] at hmap
    exact hmap
  have hcentralizes : ambientLarger ≤ centralizer := Subgroup.map_subtype_le larger
  have hlocalContains : (localSylow : Subgroup _) ≤
      (ambientLarger.subgroupOf normalizer).subgroupOf
        (Subgroup.centralizer ({element} : Set normalizer)) := by
    rw [hlocalSylow]
    intro member hmember
    change member.val.val ∈ ambientLarger
    exact Subgroup.mem_map.mpr ⟨⟨member.val.val, hcontains hmember⟩, hcontainsPrimary hmember, rfl⟩
  have hequal := localSylow.is_maximal'
    ((hlarger.map centralizer.subtype).comap_subtype.comap_subtype) hlocalContains
  rw [hlocalSylow] at hequal
  have hambient : ambientLarger = primary := by
    apply le_antisymm
    · intro member hmember
      let localMember : normalizer := ⟨member, hcontainsAmbient hmember⟩
      have hlocalCentral : localMember ∈ Subgroup.centralizer ({element} : Set normalizer) := by
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        apply Subtype.ext
        exact Subgroup.mem_centralizer_singleton_iff.mp (hcentralizes hmember)
      have hlocalMember : (⟨localMember, hlocalCentral⟩ : Subgroup.centralizer ({element} : Set normalizer)) ∈
          (primary.subgroupOf normalizer).subgroupOf
            (Subgroup.centralizer ({element} : Set normalizer)) := by
        rw [← hequal]
        exact hmember
      exact hlocalMember
    · intro member hmember
      exact Subgroup.mem_map.mpr ⟨⟨member, hcontains hmember⟩, hcontainsPrimary hmember, rfl⟩
  apply Subgroup.map_injective (Subgroup.subtype_injective centralizer)
  rw [Subgroup.map_subgroupOf_eq_of_le hcontains]
  exact hambient

theorem p_subgroup_sylow_image_conjugator {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] (primary ambient : Subgroup group)
    (hprimary : IsPGroup prime primary) (hcontains : primary ≤ ambient)
    (sylow : Sylow prime ambient)
    (hcard : Nat.card ((sylow : Subgroup ambient).map ambient.subtype) ≤ Nat.card primary) :
    ∃ conjugator : ambient, primary.map (MulAut.conj conjugator.val).toMonoidHom =
      (sylow : Subgroup ambient).map ambient.subtype := by
  obtain ⟨larger, hlarger⟩ := hprimary.comap_subtype.exists_le_sylow
  obtain ⟨conjugator, hconjugator⟩ := MulAction.exists_smul_eq ambient larger sylow
  refine ⟨conjugator, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · rintro element ⟨member, hmember, rfl⟩
    let localMember : ambient := ⟨member, hcontains hmember⟩
    have hlocalMember : localMember ∈ (larger : Subgroup ambient) := hlarger hmember
    have hconjugated : (MulAut.conj conjugator) localMember ∈ (sylow : Subgroup ambient) := by
      rw [← hconjugator]
      change (MulAut.conj conjugator) localMember ∈ MulAut.conj conjugator • (larger : Subgroup ambient)
      exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨localMember, hlocalMember, rfl⟩
    exact Subgroup.mem_map.mpr ⟨(MulAut.conj conjugator) localMember, hconjugated, rfl⟩
  · rwa [conjugation_subgroup_card]

theorem exact_defect_normalizer_fusion {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] (primary : Subgroup group) (element other : group)
    (hdefect : classDefectAt prime primary element)
    (hother : other ∈ Subgroup.centralizer (primary : Set group))
    (hclass : ConjClasses.mk element = ConjClasses.mk other) :
    ∃ conjugator : Subgroup.normalizer (primary : Set group),
      conjugator.val * element * conjugator.val⁻¹ = other := by
  obtain ⟨original, horiginal⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hclass)
  have htransported := classDefectAt_conjugation prime hdefect original
  rw [horiginal] at htransported
  obtain ⟨_, targetSylow, htargetSylow⟩ := htransported
  have htarget : (primary.map (MulAut.conj original).toMonoidHom) =
      (targetSylow : Subgroup _).map (Subgroup.centralizer ({other} : Set group)).subtype := by
    rw [htargetSylow]
    exact (Subgroup.map_subgroupOf_eq_of_le
      ((classDefectAt_conjugation prime hdefect original).1.trans_eq
        (congrArg (fun selected => Subgroup.centralizer ({selected} : Set group)) horiginal))).symm
  have hcontains : primary ≤ Subgroup.centralizer ({other} : Set group) := by
    intro member hmember
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hother member hmember)
  have hcard : Nat.card ((targetSylow : Subgroup _).map
      (Subgroup.centralizer ({other} : Set group)).subtype) ≤ Nat.card primary := by
    rw [← htarget, conjugation_subgroup_card]
  obtain ⟨adjustment, hadjustment⟩ := p_subgroup_sylow_image_conjugator prime primary _
    (classDefectAt_isPGroup hdefect) hcontains targetSylow hcard
  have hnormalizes : adjustment.val⁻¹ * original ∈ Subgroup.normalizer (primary : Set group) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change primary.map (MulAut.conj (adjustment.val⁻¹ * original)).toMonoidHom = primary
    rw [← conjugation_subgroup_map_mul, htarget, ← hadjustment,
      conjugation_subgroup_map_mul, inv_mul_cancel, conjugation_subgroup_map_one]
  refine ⟨⟨adjustment.val⁻¹ * original, hnormalizes⟩, ?_⟩
  have hfix : adjustment.val⁻¹ * other * adjustment.val = other := by
    have hcommute : Commute adjustment.val other :=
      Subgroup.mem_centralizer_singleton_iff.mp adjustment.property
    rw [hcommute.inv_left]
    group
  calc
    _ = adjustment.val⁻¹ * (original * element * original⁻¹) * adjustment.val := by group
    _ = adjustment.val⁻¹ * other * adjustment.val := by rw [horiginal]
    _ = other := hfix

theorem classDefect_normalizer_lift {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] (primary : Subgroup group)
    (localClass : ConjClasses (Subgroup.normalizer (primary : Set group)))
    (hdefect : classDefect prime localClass
      (primary.subgroupOf (Subgroup.normalizer (primary : Set group)))) :
    ∃ element : Subgroup.normalizer (primary : Set group),
      ConjClasses.mk element = localClass ∧ classDefectAt prime primary element.val := by
  obtain ⟨element, hclass, hlocal⟩ := (classDefect_iff_exists_at prime localClass _).mp hdefect
  exact ⟨element, hclass, classDefectAt_normalizer_lift prime primary element hlocal⟩

theorem exact_defect_class_intersection {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact prime.Prime] (primary : Subgroup group) (element other :
      Subgroup.normalizer (primary : Set group)) (hdefect : classDefectAt prime primary element.val) :
    (ConjClasses.mk other.val = ConjClasses.mk element.val ∧
      other.val ∈ Subgroup.centralizer (primary : Set group)) ↔
      ConjClasses.mk other = ConjClasses.mk element := by
  constructor
  · rintro ⟨hclass, hcentralizes⟩
    obtain ⟨conjugator, hconjugator⟩ := exact_defect_normalizer_fusion prime primary element.val other.val
      hdefect hcentralizes hclass.symm
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    apply IsConj.symm
    exact isConj_iff.mpr ⟨conjugator, Subtype.ext hconjugator⟩
  · intro hclass
    obtain ⟨conjugator, hconjugator⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hclass)
    have hcentralizes : element.val ∈ Subgroup.centralizer (primary : Set group) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro member hmember
      exact Subgroup.mem_centralizer_singleton_iff.mp (hdefect.1 hmember)
    have hambient := congrArg Subtype.val hconjugator
    change conjugator.val * other.val * conjugator.val⁻¹ = element.val at hambient
    constructor
    · exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨conjugator.val, hambient⟩)
    · exact (centralizer_conjugation_mem_iff primary conjugator.val other.val conjugator.property).mp
        (hambient ▸ hcentralizes)

end CFSG.TwoRankLowerBound.Helpers
