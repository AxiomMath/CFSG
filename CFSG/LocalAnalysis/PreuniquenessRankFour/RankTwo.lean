module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.Confinement

public section

open CFSG.Open

namespace CFSG.PreuniquenessRankFour.Helpers

universe u

theorem power_kernel_characteristic
    {source : Type u} [CommGroup source] (exponent : ℕ) :
    (powMonoidHom exponent : source →* source).ker.Characteristic := by
  apply Subgroup.characteristic_iff_map_le.mpr
  intro equivalence element helement
  obtain ⟨lift, hlift, rfl⟩ := helement
  change equivalence lift ^ exponent = 1
  rw [← map_pow, show lift ^ exponent = 1 from hlift, map_one]

theorem elementary_abelian_sup_of_commuting
    {ambient : Type u} [Group ambient]
    (prime : ℕ) {first second : Subgroup ambient}
    (hfirst : IsElemAbelian prime first) (hsecond : IsElemAbelian prime second)
    (hcommute : first ≤ Subgroup.centralizer (second : Set ambient)) :
    IsElemAbelian prime (first ⊔ second) := by
  let : IsMulCommutative first := hfirst.1
  let : IsMulCommutative second := hsecond.1
  let hom : first × second →* ambient :=
    { toFun := fun element => (element.1 : ambient) * (element.2 : ambient)
      map_one' := one_mul 1
      map_mul' := fun left right => by
        change ((left.1 : ambient) * (right.1 : ambient)) *
          ((left.2 : ambient) * (right.2 : ambient)) =
          ((left.1 : ambient) * (left.2 : ambient)) *
            ((right.1 : ambient) * (right.2 : ambient))
        have hmiddle := Subgroup.mem_centralizer_iff.mp
          (hcommute right.1.property) left.2 left.2.property
        calc
          _ = (left.1 : ambient) * ((right.1 : ambient) * (left.2 : ambient)) *
              (right.2 : ambient) := by group
          _ = (left.1 : ambient) * ((left.2 : ambient) * (right.1 : ambient)) *
              (right.2 : ambient) := by rw [hmiddle]
          _ = _ := by group }
  have hrange : hom.range = first ⊔ second := by
    apply le_antisymm
    · rintro element ⟨lift, rfl⟩
      exact (first ⊔ second).mul_mem
        ((show first ≤ first ⊔ second from le_sup_left) lift.1.property)
        ((show second ≤ first ⊔ second from le_sup_right) lift.2.property)
    · apply sup_le
      · intro element helement
        exact ⟨(⟨element, helement⟩, 1), mul_one element⟩
      · intro element helement
        exact ⟨(1, ⟨element, helement⟩), one_mul element⟩
  have hproduct : IsElemAbelian prime (⊤ : Subgroup (first × second)) := by
    refine ⟨inferInstance, ?_⟩
    intro element _
    apply Prod.ext
    · apply Subtype.ext
      exact hfirst.2 element.1 element.1.property
    · apply Subtype.ext
      exact hsecond.2 element.2 element.2.property
  have hmap := elementary_abelian_map prime hproduct hom
  rw [← MonoidHom.range_eq_map, hrange] at hmap
  exact hmap

theorem elementary_subgroup_eq_of_rank_bound
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) {first second : Subgroup ambient}
    (hsecond : IsElemAbelian prime second) (hcontained : first ≤ second)
    (rank : ℕ) (hcard : Nat.card first = prime ^ rank)
    (hrank : pRank prime second ≤ rank) : first = second := by
  let : Fact prime.Prime := ⟨hprime⟩
  have hgroup : IsPGroup prime second := isPGroup_iff_pow_pow_eq_one.mpr
    fun element => ⟨1, by
      apply Subtype.ext
      change element.val ^ (prime ^ 1) = 1
      simpa only [pow_one] using hsecond.2 element.val element.property⟩
  obtain ⟨secondRank, hsecondCard⟩ := IsPGroup.iff_card.mp hgroup
  have hsecondRank : secondRank ≤ rank :=
    (le_csSup (pRank_bddAbove prime hprime second)
      ⟨second, le_rfl, hsecond, hsecondCard⟩).trans hrank
  apply Subgroup.eq_of_le_of_card_ge hcontained
  rw [hcard, hsecondCard]
  exact Nat.pow_le_pow_right hprime.pos hsecondRank

theorem center_rank_two_has_characteristic_elementary
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (subgroup : Subgroup ambient)
    (hrank : pRank prime
      ((Subgroup.center subgroup).map subgroup.subtype) = 2) :
    ∃ elementary : Subgroup subgroup,
      elementary.Characteristic ∧
      IsElemAbelian prime (elementary.map subgroup.subtype) ∧
      Nat.card (elementary.map subgroup.subtype) = prime ^ 2 ∧
      elementary ≤ Subgroup.center subgroup := by
  let center := Subgroup.center subgroup
  let : CommGroup center := IsMulCommutative.instCommGroup
  let kernel := (powMonoidHom prime : center →* center).ker
  let elementary := kernel.map center.subtype
  have hkernelCharacteristic : kernel.Characteristic := power_kernel_characteristic prime
  let : kernel.Characteristic := hkernelCharacteristic
  have helementaryCharacteristic : elementary.Characteristic := inferInstance
  have helementaryCenter : elementary ≤ center := Subgroup.map_subtype_le kernel
  have hkernelElementary : IsElemAbelian prime kernel := by
    refine ⟨inferInstance, ?_⟩
    intro element helement
    exact helement
  have helementary := elementary_abelian_map prime hkernelElementary center.subtype
  have hambientElementary := elementary_abelian_map prime helementary subgroup.subtype
  obtain ⟨witness, hwitnessCenter, hwitnessElementary, hwitnessCard⟩ :=
    pRank_attained prime hprime (center.map subgroup.subtype)
  have hwitnessContained : witness ≤ elementary.map subgroup.subtype := by
    intro element helement
    obtain ⟨lift, hlift, rfl⟩ := hwitnessCenter helement
    refine ⟨lift, ?_, rfl⟩
    refine ⟨⟨lift, hlift⟩, ?_, rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hwitnessElementary.2 (lift : ambient) helement
  have helementaryEq : witness = elementary.map subgroup.subtype :=
    elementary_subgroup_eq_of_rank_bound prime hprime hambientElementary hwitnessContained
      2 (by simpa only [center, hrank] using hwitnessCard)
      ((pRank_mono prime hprime (Subgroup.map_mono helementaryCenter)).trans hrank.le)
  refine ⟨elementary, helementaryCharacteristic, hambientElementary, ?_,
    helementaryCenter⟩
  rw [← helementaryEq]
  simpa only [center, hrank] using hwitnessCard

theorem escaping_rank_two_center_bound_or_elementary
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) {sylow overgroup subgroup : Subgroup ambient}
    (hcore : GLBWeakCore prime sylow ≤ overgroup)
    (hcontained : subgroup ≤ sylow) (hrank : pRank prime subgroup = 2)
    (hescape : ¬ Subgroup.normalizer (subgroup : Set ambient) ≤ overgroup) :
    pRank prime ((Subgroup.center subgroup).map subgroup.subtype) ≤ 1 ∨
      ∃ elementary : Subgroup ambient, elementary ≤ subgroup ∧
        IsElemAbelian prime elementary ∧ Nat.card elementary = prime ^ 2 ∧
        ¬ Subgroup.normalizer (elementary : Set ambient) ≤ overgroup ∧
        ∀ extension : Subgroup ambient, elementary ≤ extension → extension ≤ sylow →
          IsElemAbelian prime extension → extension = elementary := by
  by_cases hsmall : pRank prime ((Subgroup.center subgroup).map subgroup.subtype) ≤ 1
  · exact Or.inl hsmall
  have hcenterRank : pRank prime ((Subgroup.center subgroup).map subgroup.subtype) = 2 := by
    have hbound := pRank_mono prime hprime (Subgroup.map_subtype_le
      (Subgroup.center subgroup))
    omega
  obtain ⟨localElementary, hcharacteristic, helementary, hcard, _⟩ :=
    center_rank_two_has_characteristic_elementary prime hprime subgroup hcenterRank
  let : localElementary.Characteristic := hcharacteristic
  let elementary := localElementary.map subgroup.subtype
  have helementaryContained : elementary ≤ subgroup := Subgroup.map_subtype_le localElementary
  have helementaryEscape : ¬ Subgroup.normalizer (elementary : Set ambient) ≤ overgroup := by
    intro hnormalizer
    exact hescape ((normalizer_le_normalizer_characteristic localElementary
      hcharacteristic).trans hnormalizer)
  refine Or.inr ⟨elementary, helementaryContained, helementary, hcard, helementaryEscape, ?_⟩
  intro extension hextends hextensionContained hextensionElementary
  have helementaryRank : 2 ≤ pRank prime elementary :=
    le_csSup (pRank_bddAbove prime hprime elementary)
      ⟨elementary, le_rfl, helementary, hcard⟩
  have hjoinBound : pRank prime (elementary ⊔ (sylow ⊓
      Subgroup.centralizer (elementary : Set ambient))) ≤ 2 := by
    by_contra hlarge
    exact helementaryEscape ((normalizer_le_weakCore prime
      (helementaryContained.trans hcontained) helementaryRank (by omega)).trans hcore)
  have hextensionCentralizer : extension ≤ Subgroup.centralizer (elementary : Set ambient) := by
    intro element helement
    apply Subgroup.mem_centralizer_iff.mpr
    intro member hmember
    let : IsMulCommutative extension := hextensionElementary.1
    let : CommGroup extension := IsMulCommutative.instCommGroup
    exact congrArg Subtype.val (mul_comm (⟨member, hextends hmember⟩ : extension)
      (⟨element, helement⟩ : extension))
  exact (elementary_subgroup_eq_of_rank_bound prime hprime hextensionElementary hextends
    2 hcard ((pRank_mono prime hprime
      ((le_inf hextensionContained hextensionCentralizer).trans le_sup_right)).trans
      hjoinBound)).symm

theorem fullCore_le_of_central_elementary_rank_two
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime)
    (sylow : Sylow prime ambient) {overgroup central : Subgroup ambient}
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hsylowRank : 3 ≤ pRank prime (sylow : Subgroup ambient))
    (hcentral : central ≤ sylow) (hcentralCommute :
      central ≤ Subgroup.centralizer (sylow : Set ambient))
    (helementary : IsElemAbelian prime central) (hcard : Nat.card central = prime ^ 2) :
    GLBCore prime 2 (sylow : Subgroup ambient) ≤ overgroup := by
  by_contra hescape
  obtain ⟨subgroup, hcontained, hrank, hjoinRank, _, hnormalizer⟩ :=
    fullCore_escape_of_weakCore_local prime hprime (sylow : Subgroup ambient) overgroup
      hcore hescape
  obtain ⟨witness, hwitness, hwitnessElementary, hwitnessCard⟩ :=
    pRank_attained prime hprime subgroup
  have hcentralWitness : central ≤ Subgroup.centralizer (witness : Set ambient) :=
    hcentralCommute.trans (Subgroup.centralizer_le (hwitness.trans hcontained))
  have hjoinElementary := elementary_abelian_sup_of_commuting prime
    hwitnessElementary helementary (Subgroup.le_centralizer_iff.mp hcentralWitness)
  have hjoinContained : witness ⊔ central ≤ subgroup ⊔
      ((sylow : Subgroup ambient) ⊓ Subgroup.centralizer (subgroup : Set ambient)) := by
    apply sup_le
    · exact hwitness.trans le_sup_left
    · exact (le_inf hcentral
        (hcentralCommute.trans (Subgroup.centralizer_le hcontained))).trans le_sup_right
  have hwitnessEq : witness = witness ⊔ central :=
    elementary_subgroup_eq_of_rank_bound prime hprime hjoinElementary le_sup_left 2
      (by simpa only [hrank] using hwitnessCard)
      ((pRank_mono prime hprime hjoinContained).trans hjoinRank.le)
  have hcentralSubgroup : central ≤ subgroup :=
    (hwitnessEq.symm ▸ (show central ≤ witness ⊔ central from le_sup_right)).trans hwitness
  have hnormalizesCentral : Subgroup.normalizer (subgroup : Set ambient) ≤
      Subgroup.normalizer (central : Set ambient) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro element helement member hmember
    let equivalence := MulAut.conj element
    have hmapSubgroup : subgroup.map equivalence.toMonoidHom = subgroup :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp helement
    have hcentralMap : central.map equivalence.toMonoidHom ≤ subgroup := by
      rw [← hmapSubgroup]
      exact Subgroup.map_mono hcentralSubgroup
    have hcommuteMap : central ≤
        Subgroup.centralizer (central.map equivalence.toMonoidHom : Set ambient) :=
      hcentralCommute.trans (Subgroup.centralizer_le (hcentralMap.trans hcontained))
    have hmapElementary := elementary_abelian_map prime helementary equivalence.toMonoidHom
    have hsupElementary := elementary_abelian_sup_of_commuting prime helementary
      hmapElementary hcommuteMap
    have hsupEq : central = central ⊔ central.map equivalence.toMonoidHom :=
      elementary_subgroup_eq_of_rank_bound prime hprime hsupElementary le_sup_left 2 hcard
        ((pRank_mono prime hprime (sup_le hcentralSubgroup hcentralMap)).trans hrank.le)
    exact (hsupEq.symm ▸ (show central.map equivalence.toMonoidHom ≤
      central ⊔ central.map equivalence.toMonoidHom from le_sup_right))
        (Subgroup.mem_map_of_mem equivalence.toMonoidHom hmember)
  have hcentralRank : 2 ≤ pRank prime central :=
    le_csSup (pRank_bddAbove prime hprime central) ⟨central, le_rfl, helementary, hcard⟩
  have hcentralJoin : 3 ≤ pRank prime (central ⊔ ((sylow : Subgroup ambient) ⊓
      Subgroup.centralizer (central : Set ambient))) := by
    apply hsylowRank.trans
    apply pRank_mono prime hprime
    exact (le_inf le_rfl (Subgroup.le_centralizer_iff.mp hcentralCommute)).trans le_sup_right
  exact hnormalizer (hnormalizesCentral.trans
    ((normalizer_le_weakCore prime hcentral hcentralRank hcentralJoin).trans hcore))

theorem fullCore_escape_sylow_center_rank_le_one
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime)
    (sylow : Sylow prime ambient) {overgroup : Subgroup ambient}
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hsylowRank : 3 ≤ pRank prime (sylow : Subgroup ambient))
    (hescape : ¬ GLBCore prime 2 (sylow : Subgroup ambient) ≤ overgroup) :
    pRank prime ((Subgroup.center (sylow : Subgroup ambient)).map
      (sylow : Subgroup ambient).subtype) ≤ 1 := by
  let : Fact prime.Prime := ⟨hprime⟩
  by_contra hlarge
  obtain ⟨elementary, helementaryContained, helementary, hcard⟩ := pRank_attained prime hprime
    ((Subgroup.center (sylow : Subgroup ambient)).map (sylow : Subgroup ambient).subtype)
  obtain ⟨central, _, hcentralCard⟩ :=
    Sylow.exists_subgroup_le_card_pow_prime_of_le_card (n := 2) hprime
      (IsPGroup.of_card hcard) (H := (⊤ : Subgroup elementary))
      (by
        rw [Subgroup.card_top, hcard]
        exact Nat.pow_le_pow_right hprime.pos (show 2 ≤ pRank prime
          ((Subgroup.center (sylow : Subgroup ambient)).map
            (sylow : Subgroup ambient).subtype) by omega))
  have hcentralElementary : IsElemAbelian prime (central.map elementary.subtype) := by
    let : IsMulCommutative elementary := helementary.1
    apply elementary_abelian_map prime (elementary := central)
    refine ⟨inferInstance, ?_⟩
    intro element _
    apply Subtype.ext
    exact helementary.2 element.val element.property
  have hcenterContained : central.map elementary.subtype ≤
      (Subgroup.center (sylow : Subgroup ambient)).map (sylow : Subgroup ambient).subtype :=
    (Subgroup.map_subtype_le central).trans helementaryContained
  have hcentralContained : central.map elementary.subtype ≤ sylow :=
    hcenterContained.trans (Subgroup.map_subtype_le (Subgroup.center (sylow : Subgroup ambient)))
  have hcentralCommute : central.map elementary.subtype ≤
      Subgroup.centralizer (sylow : Set ambient) := by
    intro element helement
    obtain ⟨lift, hlift, rfl⟩ := hcenterContained helement
    apply Subgroup.mem_centralizer_iff.mpr
    intro other hother
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hlift (⟨other, hother⟩ : (sylow : Subgroup ambient)))
  apply hescape
  exact fullCore_le_of_central_elementary_rank_two prime hprime sylow hcore hsylowRank
    hcentralContained hcentralCommute hcentralElementary
      (by rw [Subgroup.card_map_of_injective Subtype.val_injective, hcentralCard])

theorem commutative_pGroup_isCyclic_of_rank_le_one
    {source : Type u} [CommGroup source] [Finite source]
    (prime : ℕ) (hprime : prime.Prime) (hgroup : IsPGroup prime source)
    (hrank : pRank prime (⊤ : Subgroup source) ≤ 1) : IsCyclic source := by
  let : Fact prime.Prime := ⟨hprime⟩
  let hom : source →* source := powMonoidHom prime
  have hkernelElementary : IsElemAbelian prime hom.ker := by
    refine ⟨inferInstance, ?_⟩
    intro element helement
    exact helement
  obtain ⟨kernelRank, hkernelCard⟩ := IsPGroup.iff_card.mp (hgroup.to_subgroup hom.ker)
  have hkernelRank : kernelRank ≤ 1 :=
    (le_csSup (pRank_bddAbove prime hprime (⊤ : Subgroup source))
      ⟨hom.ker, le_top, hkernelElementary, hkernelCard⟩).trans hrank
  have hkernelBound : Nat.card hom.ker ≤ prime := by
    rw [hkernelCard]
    simpa only [pow_one] using Nat.pow_le_pow_right hprime.pos hkernelRank
  have hquotientRangeCard : Nat.card (source ⧸ hom.range) = Nat.card hom.ker := by
    apply Nat.mul_right_cancel (Nat.card_pos (α := hom.range))
    calc
      _ = Nat.card source := hom.range.card_eq_card_quotient_mul_card_subgroup.symm
      _ = Nat.card hom.range * Nat.card hom.ker := by
        rw [hom.ker.card_eq_card_quotient_mul_card_subgroup,
          Nat.card_congr (QuotientGroup.quotientKerEquivRange hom).toEquiv]
      _ = _ := Nat.mul_comm _ _
  have hrangeFrattini : hom.range ≤ frattini source := by
    rintro element ⟨lift, rfl⟩
    exact pGroup_pow_mem_frattini prime hgroup lift
  have hquotientBound : Nat.card (source ⧸ frattini source) ≤ prime := by
    change (frattini source).index ≤ prime
    apply (Subgroup.index_antitone hrangeFrattini).trans
    change Nat.card (source ⧸ hom.range) ≤ prime
    rw [hquotientRangeCard]
    exact hkernelBound
  obtain ⟨quotientRank, hquotientCard⟩ :=
    IsPGroup.iff_card.mp (hgroup.to_quotient (frattini source))
  have hquotientRank : quotientRank ≤ 1 :=
    (Nat.pow_le_pow_iff_right hprime.one_lt).mp
      (by simpa only [pow_one] using (hquotientCard ▸ hquotientBound))
  let : IsCyclic (source ⧸ frattini source) := isCyclic_of_card_dvd_prime (p := prime)
    (by
      rw [hquotientCard]
      simpa only [pow_one] using Nat.pow_dvd_pow prime hquotientRank)
  obtain ⟨generator, hgenerator⟩ :=
    isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic (source ⧸ frattini source))
  obtain ⟨lift, hlift⟩ := QuotientGroup.mk'_surjective (frattini source) generator
  have hmap : (Subgroup.zpowers lift).map (QuotientGroup.mk' (frattini source)) = ⊤ := by
    rw [MonoidHom.map_zpowers, hlift, hgenerator]
  have hgenerates : Subgroup.zpowers lift ⊔ frattini source = ⊤ := by
    rw [← QuotientGroup.ker_mk' (frattini source), ← Subgroup.comap_map_eq, hmap]
    exact Subgroup.comap_top _
  exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨lift, frattini_nongenerating hgenerates⟩

theorem fullCore_escape_sylow_center_isCyclic
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime)
    (sylow : Sylow prime ambient) {overgroup : Subgroup ambient}
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hsylowRank : 3 ≤ pRank prime (sylow : Subgroup ambient))
    (hescape : ¬ GLBCore prime 2 (sylow : Subgroup ambient) ≤ overgroup) :
    IsCyclic (Subgroup.center (sylow : Subgroup ambient)) := by
  let center := Subgroup.center (sylow : Subgroup ambient)
  let hom : center →* ambient :=
    (sylow : Subgroup ambient).subtype.comp center.subtype
  have hinjective : Function.Injective hom :=
    Subtype.val_injective.comp Subtype.val_injective
  have hcenterGroup : IsPGroup prime center := sylow.isPGroup'.to_subgroup center
  let : CommGroup center := IsMulCommutative.instCommGroup
  apply commutative_pGroup_isCyclic_of_rank_le_one (source := center) prime hprime hcenterGroup
  apply csSup_le'
  rintro rank ⟨elementary, _, helementary, hcard⟩
  apply (show pRank prime (center.map (sylow : Subgroup ambient).subtype) ≤ 1 from
    fullCore_escape_sylow_center_rank_le_one prime hprime sylow hcore hsylowRank hescape).trans'
  apply le_csSup (pRank_bddAbove prime hprime _)
  refine ⟨elementary.map hom, ?_, elementary_abelian_map prime helementary hom, ?_⟩
  · rw [show elementary.map hom =
        (elementary.map center.subtype).map (sylow : Subgroup ambient).subtype from
      (Subgroup.map_map elementary (sylow : Subgroup ambient).subtype center.subtype).symm]
    exact Subgroup.map_mono (Subgroup.map_subtype_le elementary)
  · rw [Subgroup.card_map_of_injective hinjective, hcard]

theorem subgroup_center_isCyclic_of_rank_le_one
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (subgroup : Subgroup ambient)
    (hgroup : IsPGroup prime subgroup)
    (hrank : pRank prime ((Subgroup.center subgroup).map subgroup.subtype) ≤ 1) :
    IsCyclic (Subgroup.center subgroup) := by
  let center := Subgroup.center subgroup
  let : CommGroup center := IsMulCommutative.instCommGroup
  let hom : center →* ambient := subgroup.subtype.comp center.subtype
  have hinjective : Function.Injective hom :=
    Subtype.val_injective.comp Subtype.val_injective
  apply commutative_pGroup_isCyclic_of_rank_le_one prime hprime
    (hgroup.to_subgroup center)
  apply csSup_le'
  rintro rank ⟨elementary, _, helementary, hcard⟩
  apply hrank.trans'
  apply le_csSup (pRank_bddAbove prime hprime _)
  refine ⟨elementary.map hom, ?_, elementary_abelian_map prime helementary hom, ?_⟩
  · rw [show elementary.map hom =
        (elementary.map center.subtype).map subgroup.subtype from
      (Subgroup.map_map elementary subgroup.subtype center.subtype).symm]
    exact Subgroup.map_mono (Subgroup.map_subtype_le elementary)
  · rw [Subgroup.card_map_of_injective hinjective]
    exact hcard

theorem fullCore_escape_cyclic_center_or_maximal_elementary
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime)
    (sylow : Sylow prime ambient) {overgroup : Subgroup ambient}
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hescape : ¬ GLBCore prime 2 (sylow : Subgroup ambient) ≤ overgroup) :
    (∃ subgroup : Subgroup ambient, subgroup ≤ sylow ∧ pRank prime subgroup = 2 ∧
      IsCyclic (Subgroup.center subgroup) ∧
      ¬ Subgroup.normalizer (subgroup : Set ambient) ≤ overgroup) ∨
    (∃ elementary : Subgroup ambient, elementary ≤ sylow ∧
      IsElemAbelian prime elementary ∧ Nat.card elementary = prime ^ 2 ∧
      ¬ Subgroup.normalizer (elementary : Set ambient) ≤ overgroup ∧
      ∀ extension : Subgroup ambient, elementary ≤ extension → extension ≤ sylow →
        IsElemAbelian prime extension → extension = elementary) := by
  obtain ⟨subgroup, hcontained, hrank, _, _, hnormalizer⟩ :=
    fullCore_escape_of_weakCore_local prime hprime (sylow : Subgroup ambient) overgroup
      hcore hescape
  obtain hsmall | ⟨elementary, helementaryContained, helementary, hcard,
      helementaryNormalizer, hmaximal⟩ :=
    escaping_rank_two_center_bound_or_elementary prime hprime hcore hcontained hrank hnormalizer
  · exact Or.inl ⟨subgroup, hcontained, hrank,
      subgroup_center_isCyclic_of_rank_le_one prime hprime subgroup
        (sylow.isPGroup'.to_le hcontained) hsmall, hnormalizer⟩
  · exact Or.inr ⟨elementary, helementaryContained.trans hcontained, helementary, hcard,
      helementaryNormalizer, hmaximal⟩

end CFSG.PreuniquenessRankFour.Helpers
