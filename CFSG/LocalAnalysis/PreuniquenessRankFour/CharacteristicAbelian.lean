module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.InvolutionCentralizer

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.PreuniquenessRankFour.Helpers

universe u

theorem centralPrimeTorsion_rank_eq_center_rank
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) (hprime : prime.Prime) :
    pRank prime (centralPrimeTorsion prime source) = pRank prime (Subgroup.center source) := by
  apply le_antisymm
  · apply pRank_mono prime hprime
    intro member hmember
    exact ((mem_centralPrimeTorsion prime member).mp hmember).1
  · obtain ⟨elementary, hcontained, helementary, hcard⟩ :=
      pRank_attained prime hprime (Subgroup.center source)
    apply le_csSup (pRank_bddAbove prime hprime _)
    refine ⟨elementary, ?_, helementary, hcard⟩
    intro member hmember
    exact (mem_centralPrimeTorsion prime member).mpr
      ⟨hcontained hmember, helementary.2 member hmember⟩

theorem noncyclic_commutative_pGroup_rank_at_least_two
    {source : Type u} [CommGroup source] [Finite source]
    (prime : ℕ) (hprime : prime.Prime) (hsource : IsPGroup prime source)
    (hnoncyclic : ¬ IsCyclic source) : 2 ≤ pRank prime (⊤ : Subgroup source) := by
  by_contra hsmall
  exact hnoncyclic (commutative_pGroup_isCyclic_of_rank_le_one prime hprime hsource (by omega))

theorem noncyclic_characteristic_abelian_pGroup_has_characteristic_elementary
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) (hprime : prime.Prime) (hsource : IsPGroup prime source)
    (abelian : Subgroup source) [abelian.Characteristic]
    (habelian : IsMulCommutative abelian) (hnoncyclic : ¬ IsCyclic abelian) :
    ∃ elementary : Subgroup source, elementary.Characteristic ∧
      elementary ≤ abelian ∧ IsElemAbelian prime elementary ∧ 2 ≤ pRank prime elementary := by
  let : IsMulCommutative abelian := habelian
  let : CommGroup abelian := IsMulCommutative.instCommGroup
  let torsion := centralPrimeTorsion prime abelian
  let : torsion.Characteristic := centralPrimeTorsion_characteristic prime
  let elementary := torsion.map abelian.subtype
  have htorsionRank : 2 ≤ pRank prime torsion := by
    rw [centralPrimeTorsion_rank_eq_center_rank prime hprime,
      Subgroup.center_eq_top]
    exact noncyclic_commutative_pGroup_rank_at_least_two prime hprime
      (hsource.to_subgroup abelian) hnoncyclic
  refine ⟨elementary, inferInstance, Subgroup.map_subtype_le torsion,
    elementary_abelian_map prime (centralPrimeTorsion_elementary prime) abelian.subtype, ?_⟩
  rw [pRank_map_of_injective prime hprime abelian.subtype Subtype.val_injective]
  exact htorsionRank

theorem no_large_characteristic_elementary_forces_characteristic_abelian_cyclic
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) (hprime : prime.Prime) (hsource : IsPGroup prime source)
    (hsmall : ∀ elementary : Subgroup source, elementary.Characteristic →
      IsElemAbelian prime elementary → pRank prime elementary ≤ 1)
    (abelian : Subgroup source) [abelian.Characteristic]
    (habelian : IsMulCommutative abelian) : IsCyclic abelian := by
  by_contra hnoncyclic
  obtain ⟨elementary, hcharacteristic, _, helementary, hrank⟩ :=
    noncyclic_characteristic_abelian_pGroup_has_characteristic_elementary prime hprime hsource
      abelian habelian hnoncyclic
  have hbound := hsmall elementary hcharacteristic helementary
  omega

theorem twoCore_has_cyclic_critical_center_or_large_characteristic_elementary
    {source : Type u} [Group source] [Finite source] :
    (∃ elementary : Subgroup (pCore 2 source), elementary.Characteristic ∧
      IsElemAbelian 2 elementary ∧ 2 ≤ pRank 2 elementary) ∨
    ∃ critical : Subgroup (pCore 2 source), critical.Characteristic ∧
      (frattini critical).map critical.subtype ≤ (Subgroup.center critical).map critical.subtype ∧
      ⁅(⊤ : Subgroup (pCore 2 source)), critical⁆ ≤ (Subgroup.center critical).map critical.subtype ∧
      Subgroup.centralizer (critical : Set (pCore 2 source)) =
        (Subgroup.center critical).map critical.subtype ∧ IsCyclic (Subgroup.center critical) := by
  classical
  by_cases hlarge : ∃ elementary : Subgroup (pCore 2 source), elementary.Characteristic ∧
      IsElemAbelian 2 elementary ∧ 2 ≤ pRank 2 elementary
  · exact Or.inl hlarge
  apply Or.inr
  let : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  obtain ⟨critical, hcharacteristic, hfrattini, hcommutator, hcentralizer⟩ :=
    pGroup_has_characteristic_critical_subgroup 2 (pCore_isPGroup 2 (G := source))
  let : critical.Characteristic := hcharacteristic
  let center := (Subgroup.center critical).map critical.subtype
  let : center.Characteristic := inferInstance
  have hcenterCommutative : IsMulCommutative center := IsMulCommutative.of_comm (by
    intro first second
    apply Subtype.ext
    change (first : pCore 2 source) * (second : pCore 2 source) =
      (second : pCore 2 source) * (first : pCore 2 source)
    obtain ⟨firstLift, hfirst, hfirsteq⟩ := first.property
    obtain ⟨secondLift, hsecond, hsecondeq⟩ := second.property
    rw [← hfirsteq, ← hsecondeq]
    exact congrArg (fun member : critical => (member : pCore 2 source))
      (Subgroup.mem_center_iff.mp hfirst secondLift).symm)
  have hcenterCyclic : IsCyclic center :=
    no_large_characteristic_elementary_forces_characteristic_abelian_cyclic 2 (by norm_num)
      (pCore_isPGroup 2) (fun elementary hcharacteristic helementary => by
        by_contra hnotSmall
        exact hlarge ⟨elementary, hcharacteristic, helementary, by omega⟩) center hcenterCommutative
  have hcyclic : IsCyclic (Subgroup.center critical) :=
    ((Subgroup.center critical).equivMapOfInjective critical.subtype Subtype.val_injective).isCyclic.mpr hcenterCyclic
  exact ⟨critical, hcharacteristic, hfrattini, hcommutator, hcentralizer, hcyclic⟩

theorem escaping_primeCore_quotient_normal_pGroup_characteristic_abelian_isCyclic
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup source : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hrank : 3 ≤ pRank prime (source ⊓ overgroup))
    (hescape : ¬ source ≤ overgroup)
    [((GLBPrimeCore prime source).subgroupOf source).Normal]
    (normal : Subgroup (source ⧸ (GLBPrimeCore prime source).subgroupOf source))
    [normal.Normal] (hnormal : IsPGroup prime normal)
    (abelian : Subgroup normal) [abelian.Characteristic]
    (habelian : IsMulCommutative abelian) : IsCyclic abelian := by
  apply no_large_characteristic_elementary_forces_characteristic_abelian_cyclic
    prime hprime hnormal _ abelian habelian
  intro elementary hcharacteristic helementary
  let : elementary.Characteristic := hcharacteristic
  let image := elementary.map normal.subtype
  let : image.Normal := inferInstance
  have himageElementary : IsElemAbelian prime image :=
    elementary_abelian_map prime helementary normal.subtype
  have hbound := escaping_rank_three_primeCore_quotient_normal_elementary_rank_le_one
    prime hprime sylow hsylow hcore hrank hescape image himageElementary
  rw [pRank_map_of_injective prime hprime normal.subtype Subtype.val_injective] at hbound
  exact hbound

theorem escaping_primeCore_quotient_normal_pGroup_center_isCyclic
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup source : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hrank : 3 ≤ pRank prime (source ⊓ overgroup))
    (hescape : ¬ source ≤ overgroup)
    [((GLBPrimeCore prime source).subgroupOf source).Normal]
    (normal : Subgroup (source ⧸ (GLBPrimeCore prime source).subgroupOf source))
    [normal.Normal] (hnormal : IsPGroup prime normal) : IsCyclic (Subgroup.center normal) :=
  escaping_primeCore_quotient_normal_pGroup_characteristic_abelian_isCyclic prime hprime sylow
    hsylow hcore hrank hescape normal hnormal (Subgroup.center normal) inferInstance

theorem escaping_primeCore_quotient_normal_pGroup_critical_center_isCyclic
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup source : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hrank : 3 ≤ pRank prime (source ⊓ overgroup))
    (hescape : ¬ source ≤ overgroup)
    [((GLBPrimeCore prime source).subgroupOf source).Normal]
    (normal : Subgroup (source ⧸ (GLBPrimeCore prime source).subgroupOf source))
    [normal.Normal] (hnormal : IsPGroup prime normal)
    (critical : Subgroup normal) [critical.Characteristic] : IsCyclic (Subgroup.center critical) := by
  let center := (Subgroup.center critical).map critical.subtype
  let : center.Characteristic := inferInstance
  have hcommutative : IsMulCommutative center := IsMulCommutative.of_comm (by
    intro first second
    apply Subtype.ext
    change (first : normal) * (second : normal) = (second : normal) * (first : normal)
    obtain ⟨firstLift, hfirst, hfirsteq⟩ := first.property
    obtain ⟨secondLift, hsecond, hsecondeq⟩ := second.property
    rw [← hfirsteq, ← hsecondeq]
    exact congrArg (fun member : critical => (member : normal))
      (Subgroup.mem_center_iff.mp hfirst secondLift).symm)
  have hcyclic : IsCyclic center :=
    escaping_primeCore_quotient_normal_pGroup_characteristic_abelian_isCyclic prime hprime sylow
      hsylow hcore hrank hescape normal hnormal center hcommutative
  exact ((Subgroup.center critical).equivMapOfInjective critical.subtype Subtype.val_injective).isCyclic.mpr hcyclic

theorem maximal_local_without_large_characteristic_elementary_has_involution_and_common_sylow
    {ambient : Type u} [Group ambient] [Finite ambient]
    (hchar : IsCharTwoType ambient)
    {localGroup : Subgroup ambient} (hmaximal : GLBIsMaxTwoLocal localGroup)
    (hsmall : ∀ elementary : Subgroup (pCore 2 localGroup), elementary.Characteristic →
      IsElemAbelian 2 elementary → pRank 2 elementary ≤ 1) :
    (∃ subgroup : Subgroup ambient, Nat.card subgroup = 2 ∧
      subgroup ≤ pCoreOf 2 localGroup ∧ Subgroup.centralizer (subgroup : Set ambient) = localGroup) ∧
    ∀ sylow : Sylow 2 localGroup, ∃ ambientSylow : Sylow 2 ambient,
      (ambientSylow : Subgroup ambient) = (sylow : Subgroup localGroup).map localGroup.subtype := by
  rcases twoCore_has_cyclic_critical_center_or_large_characteristic_elementary
      (source := localGroup) with hlarge | hcritical
  · obtain ⟨elementary, hcharacteristic, helementary, hrank⟩ := hlarge
    have hbound := hsmall elementary hcharacteristic helementary
    omega
  obtain ⟨critical, hcharacteristic, _, _, hcentralizer, hcenter⟩ := hcritical
  let : critical.Characteristic := hcharacteristic
  have hselfcentralizer : Subgroup.centralizer (critical : Set (pCore 2 localGroup)) ≤ critical := by
    rw [hcentralizer]
    exact Subgroup.map_subtype_le _
  let : Nontrivial (pCore 2 localGroup) := (pCore 2 localGroup).nontrivial_iff_ne_bot.mpr
    (charTwo_local_twoCore_nontrivial localGroup hmaximal.1)
  let : Nontrivial critical := critical.nontrivial_iff_ne_bot.mpr
    (characteristic_critical_subgroup_nontrivial critical inferInstance hselfcentralizer)
  refine ⟨maximal_local_cyclic_critical_center_has_order_two_centralizer
    hmaximal critical hcenter inferInstance, ?_⟩
  intro sylow
  exact maximal_local_cyclic_critical_center_has_common_two_sylow
    hchar hmaximal critical hselfcentralizer hcenter inferInstance sylow

end CFSG.PreuniquenessRankFour.Helpers
