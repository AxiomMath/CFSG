module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.CriticalSymplectic

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.PreuniquenessRankFour.Helpers

universe u

theorem order_two_subgroup_normalizer_eq_centralizer
    {ambient : Type u} [Group ambient]
    (subgroup : Subgroup ambient) (hcard : Nat.card subgroup = 2) :
    Subgroup.normalizer (subgroup : Set ambient) = Subgroup.centralizer (subgroup : Set ambient) := by
  let : Finite subgroup := Nat.finite_of_card_ne_zero (by omega)
  let : MulDistribMulAction (Subgroup.normalizer (subgroup : Set ambient)) subgroup :=
    MulDistribMulAction.compHom subgroup subgroup.normalizerMonoidHom
  apply le_antisymm _ (Subgroup.centralizer_le_normalizer _)
  intro scalar hscalar
  apply Subgroup.mem_centralizer_iff.mpr
  intro member hmember
  have hfixed := prime_card_two_group_action_trivial hcard
    (⟨scalar, hscalar⟩ : Subgroup.normalizer (subgroup : Set ambient)) (⟨member, hmember⟩ : subgroup)
  have hvalues := congrArg Subtype.val hfixed
  change scalar * member * scalar⁻¹ = member at hvalues
  have hcommute := congrArg (fun value : ambient => value * scalar) hvalues
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hcommute.symm

theorem maximal_local_characteristic_order_two_subgroup_centralizer
    {ambient : Type u} [Group ambient]
    {localGroup : Subgroup ambient} (hmaximal : GLBIsMaxTwoLocal localGroup)
    (subgroup : Subgroup localGroup) (hcharacteristic : subgroup.Characteristic)
    (hcard : Nat.card subgroup = 2) :
    Subgroup.centralizer (subgroup.map localGroup.subtype : Set ambient) = localGroup := by
  let mapped := subgroup.map localGroup.subtype
  have hmappedCard : Nat.card mapped = 2 := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective]
    exact hcard
  have hnontrivial : mapped ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hmappedCard
    omega
  have hlocal : IsTwoLocal (Subgroup.normalizer (mapped : Set ambient)) :=
    ⟨mapped, hnontrivial, IsPGroup.of_card (n := 1) (by simpa using hmappedCard), rfl⟩
  have hnormalizer : Subgroup.normalizer (mapped : Set ambient) = localGroup :=
    hmaximal.2 _ hlocal (Subgroup.le_normalizer.trans
      (normalizer_le_normalizer_characteristic subgroup hcharacteristic))
  rw [← order_two_subgroup_normalizer_eq_centralizer mapped hmappedCard]
  exact hnormalizer

theorem maximal_local_cyclic_critical_center_has_order_two_centralizer
    {ambient : Type u} [Group ambient] [Finite ambient]
    {localGroup : Subgroup ambient} (hmaximal : GLBIsMaxTwoLocal localGroup)
    (critical : Subgroup (pCore 2 localGroup)) [critical.Characteristic]
    (hcenter : IsCyclic (Subgroup.center critical)) (hnontrivial : Nontrivial critical) :
    ∃ subgroup : Subgroup ambient, Nat.card subgroup = 2 ∧
      subgroup ≤ pCoreOf 2 localGroup ∧
        Subgroup.centralizer (subgroup : Set ambient) = localGroup := by
  let : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let : (pCore 2 localGroup).Characteristic := pCore_characteristic 2
  let : (centralPrimeTorsion 2 critical).Characteristic := centralPrimeTorsion_characteristic 2
  let torsionCore := (centralPrimeTorsion 2 critical).map critical.subtype
  let torsionLocal := torsionCore.map (pCore 2 localGroup).subtype
  let : torsionCore.Characteristic := inferInstance
  let : torsionLocal.Characteristic := inferInstance
  have hcard : Nat.card torsionLocal = 2 := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective,
      Subgroup.card_map_of_injective Subtype.val_injective]
    exact centralPrimeTorsion_card_eq_prime_of_cyclic_center 2
      ((pCore_isPGroup 2).to_subgroup critical) hcenter hnontrivial
  refine ⟨torsionLocal.map localGroup.subtype,
    (Subgroup.card_map_of_injective Subtype.val_injective).trans hcard, ?_, ?_⟩
  · exact Subgroup.map_mono (Subgroup.map_subtype_le torsionCore)
  · exact maximal_local_characteristic_order_two_subgroup_centralizer hmaximal torsionLocal inferInstance hcard

theorem selfcentralizing_critical_cyclic_center_whole_center_isCyclic
    {source : Type u} [Group source]
    (critical : Subgroup source)
    (hcritical : Subgroup.centralizer (critical : Set source) ≤ critical)
    (hcenter : IsCyclic (Subgroup.center critical)) : IsCyclic (Subgroup.center source) := by
  let : IsCyclic (Subgroup.center critical) := hcenter
  have hcontained : Subgroup.center source ≤ (Subgroup.center critical).map critical.subtype := by
    rw [subgroup_center_image_eq_inf_centralizer]
    exact le_inf ((Subgroup.center_le_centralizer _).trans hcritical) (Subgroup.center_le_centralizer _)
  have himage : IsCyclic ((Subgroup.center critical).map critical.subtype) :=
    ((Subgroup.center critical).equivMapOfInjective critical.subtype Subtype.val_injective).isCyclic.mp inferInstance
  let : IsCyclic ((Subgroup.center critical).map critical.subtype) := himage
  exact Subgroup.isCyclic_of_le hcontained

theorem normal_order_two_subgroup_with_cyclic_center_normalizer_eq
    {ambient : Type u} [Group ambient] [Finite ambient]
    (group subgroup : Subgroup ambient) (hgroup : IsPGroup 2 group)
    (hcenter : IsCyclic (Subgroup.center group)) (hsubgroup : subgroup ≤ group)
    (hcard : Nat.card subgroup = 2) (hnormal : (subgroup.subgroupOf group).Normal) :
    Subgroup.normalizer (group : Set ambient) ≤ Subgroup.normalizer (subgroup : Set ambient) := by
  let : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hcentral : subgroup ≤ Subgroup.centralizer (group : Set ambient) := by
    apply Subgroup.le_centralizer_iff.mpr
    rw [← order_two_subgroup_normalizer_eq_centralizer subgroup hcard]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hsubgroup).mp hnormal
  have hlocalCenter : subgroup.subgroupOf group ≤ Subgroup.center group := by
    intro member hmember
    apply Subgroup.mem_center_iff.mpr
    intro other
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hcentral hmember) _ other.property)
  have hlocalTorsion : subgroup.subgroupOf group ≤ centralPrimeTorsion 2 group := by
    intro member hmember
    apply (mem_centralPrimeTorsion 2 _).mpr
    refine ⟨hlocalCenter hmember, ?_⟩
    apply Subtype.ext
    have hpower : (⟨(member : ambient), hmember⟩ : subgroup) ^ 2 = 1 := by
      rw [← hcard]
      exact pow_card_eq_one'
    exact congrArg (fun value : subgroup => (value : ambient)) hpower
  have hnontrivial : Nontrivial group := by
    have hcardLe := Nat.card_le_card_of_injective (Subgroup.inclusion hsubgroup)
      (Subgroup.inclusion_injective hsubgroup)
    exact Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have htorsionCard := centralPrimeTorsion_card_eq_prime_of_cyclic_center 2 hgroup hcenter hnontrivial
  have hlocalCard : Nat.card (subgroup.subgroupOf group) = 2 := by
    rw [Nat.card_congr (subgroup.subgroupOfEquivOfLe hsubgroup).toEquiv, hcard]
  have hequal : subgroup.subgroupOf group = centralPrimeTorsion 2 group :=
    Subgroup.eq_of_le_of_card_ge hlocalTorsion (by rw [hlocalCard, htorsionCard])
  have hmap : (centralPrimeTorsion 2 group).map group.subtype = subgroup := by
    rw [← hequal, Subgroup.map_subgroupOf_eq_of_le hsubgroup]
  rw [← hmap]
  exact normalizer_le_normalizer_characteristic _ (centralPrimeTorsion_characteristic 2)

theorem local_sylow_with_confined_normalizer_is_ambient_sylow
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) [Fact prime.Prime] (localGroup : Subgroup ambient)
    (localSylow : Sylow prime localGroup)
    (hnormalizer : Subgroup.normalizer
      ((localSylow : Subgroup localGroup).map localGroup.subtype : Set ambient) ≤ localGroup) :
    ∃ ambientSylow : Sylow prime ambient,
      (ambientSylow : Subgroup ambient) = (localSylow : Subgroup localGroup).map localGroup.subtype := by
  let mapped := (localSylow : Subgroup localGroup).map localGroup.subtype
  obtain ⟨ambientSylow, hcontained⟩ := (localSylow.isPGroup'.map localGroup.subtype).exists_le_sylow
  let subgroup := mapped.subgroupOf (ambientSylow : Subgroup ambient)
  let : Group.IsNilpotent (ambientSylow : Subgroup ambient) := ambientSylow.isPGroup'.isNilpotent
  have hnormalizerInside : Subgroup.normalizer (subgroup : Set (ambientSylow : Subgroup ambient)) = subgroup := by
    apply le_antisymm _ Subgroup.le_normalizer
    rw [← Subgroup.subgroupOf_normalizer_eq hcontained]
    intro member hmember
    have hmemberLocal : (member : ambient) ∈ localGroup := hnormalizer hmember
    have hlocalIntersectionGroup : IsPGroup prime
        ((ambientSylow : Subgroup ambient).subgroupOf localGroup) := ambientSylow.isPGroup'.comap_subtype
    have hlocalContains : (localSylow : Subgroup localGroup) ≤
        (ambientSylow : Subgroup ambient).subgroupOf localGroup := by
      intro scalar hscalar
      exact hcontained (Subgroup.mem_map_of_mem localGroup.subtype hscalar)
    have hlocalEqual := localSylow.is_maximal' hlocalIntersectionGroup hlocalContains
    have hmemberSylow : (⟨(member : ambient), hmemberLocal⟩ : localGroup) ∈
        (localSylow : Subgroup localGroup) := hlocalEqual ▸ member.property
    exact Subgroup.mem_map_of_mem localGroup.subtype hmemberSylow
  have htop := (normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := (ambientSylow : Subgroup ambient))))
      subgroup hnormalizerInside
  have hequal : mapped = (ambientSylow : Subgroup ambient) :=
    le_antisymm hcontained (Subgroup.subgroupOf_eq_top.mp htop)
  exact ⟨ambientSylow, hequal.symm⟩

theorem selfcentralizing_twoCore_cyclic_critical_center_sylow_center_isCyclic
    {source : Type u} [Group source] [Finite source]
    (hselfcentralizer : Subgroup.centralizer (pCore 2 source : Set source) ≤ pCore 2 source)
    (critical : Subgroup (pCore 2 source))
    (hcritical : Subgroup.centralizer (critical : Set (pCore 2 source)) ≤ critical)
    (hcenter : IsCyclic (Subgroup.center critical)) (sylow : Sylow 2 source) :
    IsCyclic (Subgroup.center (sylow : Subgroup source)) := by
  let : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let : (pCore 2 source).Normal := pCore_normal 2
  let : IsCyclic (Subgroup.center critical) := hcenter
  have hcoreSylow : pCore 2 source ≤ (sylow : Subgroup source) :=
    (pCore_isPGroup 2).le_sylow_of_normal sylow
  have hcore : ∀ member : Subgroup.center (sylow : Subgroup source),
      ((member : (sylow : Subgroup source)) : source) ∈ pCore 2 source := by
    intro member
    apply hselfcentralizer
    apply Subgroup.mem_centralizer_iff.mpr
    intro other hother
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp member.property)
      (⟨other, hcoreSylow hother⟩ : (sylow : Subgroup source)))
  let coreMember : Subgroup.center (sylow : Subgroup source) → pCore 2 source :=
    fun member => ⟨((member : (sylow : Subgroup source)) : source), hcore member⟩
  have hcriticalMember : ∀ member, coreMember member ∈ critical := by
    intro member
    apply hcritical
    apply Subgroup.mem_centralizer_iff.mpr
    intro other hother
    apply Subtype.ext
    exact congrArg (fun value : (sylow : Subgroup source) => (value : source)) ((Subgroup.mem_center_iff.mp member.property)
      (⟨(other : source), hcoreSylow other.property⟩ : (sylow : Subgroup source)))
  let criticalMember : Subgroup.center (sylow : Subgroup source) → critical :=
    fun member => ⟨coreMember member, hcriticalMember member⟩
  have hcriticalCenter : ∀ member, criticalMember member ∈ Subgroup.center critical := by
    intro member
    apply Subgroup.mem_center_iff.mpr
    intro other
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun value : (sylow : Subgroup source) => (value : source)) ((Subgroup.mem_center_iff.mp member.property)
      (⟨((other : pCore 2 source) : source), hcoreSylow (other : pCore 2 source).property⟩ :
        (sylow : Subgroup source)))
  let hom : Subgroup.center (sylow : Subgroup source) →* Subgroup.center critical :=
    { toFun := fun member => ⟨criticalMember member, hcriticalCenter member⟩
      map_one' := by apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; rfl
      map_mul' := fun _ _ => by apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; rfl }
  have hinjective : Function.Injective hom := by
    intro first second hequal
    have hvalues : ((first : (sylow : Subgroup source)) : source) =
        ((second : (sylow : Subgroup source)) : source) :=
      congrArg (fun member : Subgroup.center critical =>
        (((member : critical) : pCore 2 source) : source)) hequal
    exact Subtype.ext (Subtype.ext hvalues)
  exact isCyclic_of_injective hom hinjective

theorem involution_centralizer_with_cyclic_sylow_center_has_common_sylow
    {ambient : Type u} [Group ambient] [Finite ambient]
    (localGroup subgroup : Subgroup ambient) (hcard : Nat.card subgroup = 2)
    (hcentralizer : Subgroup.centralizer (subgroup : Set ambient) = localGroup)
    (hcontained : subgroup ≤ localGroup) (sylow : Sylow 2 localGroup)
    (hcenter : IsCyclic (Subgroup.center (sylow : Subgroup localGroup))) :
    ∃ ambientSylow : Sylow 2 ambient,
      (ambientSylow : Subgroup ambient) = (sylow : Subgroup localGroup).map localGroup.subtype := by
  let : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let localSubgroup := subgroup.subgroupOf localGroup
  have hlocalGroup : IsPGroup 2 localSubgroup :=
    (IsPGroup.of_card (p := 2) (n := 1) (by simpa using hcard)).comap_subtype
  let : localSubgroup.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcontained).mpr
      (hcentralizer ▸ Subgroup.centralizer_le_normalizer _)
  have hsubgroupSylow : subgroup ≤ (sylow : Subgroup localGroup).map localGroup.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hcontained]
    exact Subgroup.map_mono (hlocalGroup.le_sylow_of_normal sylow)
  let mapped := (sylow : Subgroup localGroup).map localGroup.subtype
  have hequivalence := (sylow : Subgroup localGroup).equivMapOfInjective
    localGroup.subtype Subtype.val_injective
  let centerHom : Subgroup.center mapped →* Subgroup.center (sylow : Subgroup localGroup) :=
    { toFun := fun member => ⟨hequivalence.symm member, Subgroup.mem_center_iff.mpr fun other => by
        apply hequivalence.injective
        rw [map_mul, map_mul, hequivalence.apply_symm_apply]
        exact Subgroup.mem_center_iff.mp member.property (hequivalence other)⟩
      map_one' := Subtype.ext hequivalence.symm.map_one
      map_mul' := fun first second => Subtype.ext (hequivalence.symm.map_mul first second) }
  let : IsCyclic (Subgroup.center (sylow : Subgroup localGroup)) := hcenter
  have hmappedCenter : IsCyclic (Subgroup.center mapped) := isCyclic_of_injective centerHom
    (fun first second hequal => Subtype.ext (hequivalence.symm.injective (congrArg Subtype.val hequal)))
  have hnormal : (subgroup.subgroupOf mapped).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hsubgroupSylow).mpr
      ((Subgroup.map_subtype_le (sylow : Subgroup localGroup)).trans
        (hcentralizer ▸ Subgroup.centralizer_le_normalizer _))
  apply local_sylow_with_confined_normalizer_is_ambient_sylow 2 localGroup sylow
  exact (normal_order_two_subgroup_with_cyclic_center_normalizer_eq mapped subgroup
    (sylow.isPGroup'.map localGroup.subtype) hmappedCenter hsubgroupSylow hcard hnormal).trans
      ((order_two_subgroup_normalizer_eq_centralizer subgroup hcard).le.trans hcentralizer.le)

theorem maximal_local_cyclic_critical_center_has_common_two_sylow
    {ambient : Type u} [Group ambient] [Finite ambient]
    (hchar : IsCharTwoType ambient)
    {localGroup : Subgroup ambient} (hmaximal : GLBIsMaxTwoLocal localGroup)
    (critical : Subgroup (pCore 2 localGroup)) [critical.Characteristic]
    (hcritical : Subgroup.centralizer (critical : Set (pCore 2 localGroup)) ≤ critical)
    (hcenter : IsCyclic (Subgroup.center critical)) (hnontrivial : Nontrivial critical)
    (sylow : Sylow 2 localGroup) :
    ∃ ambientSylow : Sylow 2 ambient,
      (ambientSylow : Subgroup ambient) = (sylow : Subgroup localGroup).map localGroup.subtype := by
  obtain ⟨subgroup, hcard, hcontained, hcentralizer⟩ :=
    maximal_local_cyclic_critical_center_has_order_two_centralizer hmaximal critical hcenter hnontrivial
  have hsylowCenter := selfcentralizing_twoCore_cyclic_critical_center_sylow_center_isCyclic
    (charTwo_local_twoCore_selfcentralizing hchar localGroup hmaximal.1) critical hcritical hcenter sylow
  exact involution_centralizer_with_cyclic_sylow_center_has_common_sylow localGroup subgroup hcard
    hcentralizer (hcontained.trans (pCoreOf_le 2 localGroup)) sylow hsylowCenter

end CFSG.PreuniquenessRankFour.Helpers
