module

public import CFSG.Open.OrderForm
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Confinement

public section

open CFSG.Open

namespace CFSG.PreuniquenessRankFour.Helpers

universe u v

theorem pRank_map_of_injective
    {source : Type u} {target : Type v} [Group source] [Finite source]
    [Group target] [Finite target]
    (prime : ℕ) (hprime : prime.Prime) (hom : source →* target)
    (hinjective : Function.Injective hom) (subgroup : Subgroup source) :
    pRank prime (subgroup.map hom) = pRank prime subgroup := by
  apply le_antisymm
  · obtain ⟨elementary, hcontained, helementary, hcard⟩ :=
      pRank_attained prime hprime (subgroup.map hom)
    let lifted := elementary.comap hom
    have hmap : lifted.map hom = elementary :=
      Subgroup.map_comap_eq_self (hcontained.trans (by
        rintro element ⟨lift, _, rfl⟩
        exact ⟨lift, rfl⟩))
    have hlifted : lifted ≤ subgroup := by
      have hle := Subgroup.comap_mono (f := hom) hcontained
      rwa [Subgroup.comap_map_eq_self_of_injective hinjective] at hle
    have hliftedElementary : IsElemAbelian prime lifted := by
      let : IsMulCommutative elementary := helementary.1
      refine ⟨Subgroup.comap_injective_isMulCommutative elementary hinjective, ?_⟩
      intro element helement
      apply hinjective
      rw [map_pow, helementary.2 (hom element) helement, map_one]
    apply le_csSup (pRank_bddAbove prime hprime subgroup)
    refine ⟨lifted, hlifted, hliftedElementary, ?_⟩
    rw [← Subgroup.card_map_of_injective hinjective, hmap, hcard]
  · obtain ⟨elementary, hcontained, helementary, hcard⟩ :=
      pRank_attained prime hprime subgroup
    apply le_csSup (pRank_bddAbove prime hprime (subgroup.map hom))
    refine ⟨elementary.map hom, Subgroup.map_mono hcontained,
      elementary_abelian_map prime helementary hom, ?_⟩
    rw [Subgroup.card_map_of_injective hinjective, hcard]

theorem elementary_rank_le_kernel_rank_add_image_rank
    {source : Type u} {target : Type v} [Group source] [Finite source]
    [Group target] [Finite target]
    (prime : ℕ) (hprime : prime.Prime) (hom : source →* target)
    {elementary : Subgroup source} (helementary : IsElemAbelian prime elementary)
    (rank : ℕ) (hcard : Nat.card elementary = prime ^ rank) :
    rank ≤ pRank prime hom.ker + pRank prime (elementary.map hom) := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : IsMulCommutative elementary := helementary.1
  let restricted := hom.comp elementary.subtype
  have hkernelElementary : IsElemAbelian prime restricted.ker := by
    refine ⟨inferInstance, ?_⟩
    intro element _
    apply Subtype.ext
    exact helementary.2 element element.property
  have hkernelGroup : IsPGroup prime restricted.ker :=
    (IsPGroup.of_card hcard).to_subgroup restricted.ker
  have himageElementary : IsElemAbelian prime restricted.range := by
    have hrange : restricted.range = elementary.map hom := by
      exact (MonoidHom.range_comp hom elementary.subtype).trans
        (congrArg (Subgroup.map hom) elementary.range_subtype)
    exact hrange ▸ elementary_abelian_map prime helementary hom
  have himageGroup : IsPGroup prime restricted.range := by
    have hsurjective : Function.Surjective restricted.rangeRestrict :=
      restricted.rangeRestrict_surjective
    exact (IsPGroup.of_card hcard).of_surjective restricted.rangeRestrict hsurjective
  obtain ⟨kernelRank, hkernelCard⟩ := IsPGroup.iff_card.mp hkernelGroup
  obtain ⟨imageRank, himageCard⟩ := IsPGroup.iff_card.mp himageGroup
  have hsum : rank = kernelRank + imageRank := by
    have hproduct := restricted.ker.card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange restricted).toEquiv,
      hcard, hkernelCard, himageCard, ← pow_add] at hproduct
    have hequal := Nat.pow_right_injective hprime.two_le hproduct
    omega
  have hkernelAmbient : restricted.ker.map elementary.subtype ≤ hom.ker := by
    rintro element ⟨lift, hlift, rfl⟩
    exact hlift
  have hkernelRank : kernelRank ≤ pRank prime hom.ker := by
    apply le_csSup (pRank_bddAbove prime hprime hom.ker)
    refine ⟨restricted.ker.map elementary.subtype, hkernelAmbient,
      elementary_abelian_map prime hkernelElementary elementary.subtype, ?_⟩
    rw [Subgroup.card_map_of_injective Subtype.val_injective, hkernelCard]
  have himageRank : imageRank ≤ pRank prime (elementary.map hom) := by
    apply le_csSup (pRank_bddAbove prime hprime (elementary.map hom))
    refine ⟨restricted.range, ?_, himageElementary, himageCard⟩
    rintro element ⟨lift, rfl⟩
    exact ⟨lift, lift.property, rfl⟩
  omega

theorem nonabelian_simple_isQuasisimple
    (source : Type u) [Group source] [IsSimpleGroup source]
    (hnonab : ∃ first second : source, first * second ≠ second * first) :
    IsQuasisimple source := by
  have hcommutator : commutator source = ⊤ := by
    rcases (inferInstance : (commutator source).Normal).eq_bot_or_eq_top with hbot | htop
    · have hcommutative := (commutator_eq_bot_iff source).mp hbot
      obtain ⟨first, second, hnotCommute⟩ := hnonab
      exact False.elim (hnotCommute ((isMulCommutative_iff.mp hcommutative) first second))
    · exact htop
  have hcenter : Subgroup.center source = ⊥ := by
    rcases (inferInstance : (Subgroup.center source).Normal).eq_bot_or_eq_top with hbot | htop
    · exact hbot
    · have hcommutative := Subgroup.center_eq_top_iff.mp htop
      obtain ⟨first, second, hnotCommute⟩ := hnonab
      exact False.elim (hnotCommute ((isMulCommutative_iff.mp hcommutative) first second))
  refine ⟨hcommutator, ?_⟩
  let equivalence := (QuotientGroup.congr (Subgroup.center source) (⊥ : Subgroup source)
    (MulEquiv.refl source) (by simpa using hcenter)).trans QuotientGroup.quotientBot
  exact equivalence.isSimpleGroup

theorem maximal_normal_quotient_isSimpleGroup
    {source : Type u} [Group source] (normal : Subgroup source) [normal.Normal]
    (hmaximal : Maximal (fun candidate : Subgroup source => candidate.Normal ∧ candidate ≠ ⊤)
      normal) : IsSimpleGroup (source ⧸ normal) := by
  let : Nontrivial (source ⧸ normal) := QuotientGroup.nontrivial_iff.mpr hmaximal.1.2
  constructor
  intro subgroup hnormal
  let : subgroup.Normal := hnormal
  have hcontained : normal ≤ subgroup.comap (QuotientGroup.mk' normal) := by
    intro element helement
    change (QuotientGroup.mk' normal) element ∈ subgroup
    rw [show (QuotientGroup.mk' normal) element = 1 from
      (QuotientGroup.eq_one_iff element).mpr helement]
    exact subgroup.one_mem
  by_cases htop : subgroup.comap (QuotientGroup.mk' normal) = ⊤
  · right
    apply Subgroup.comap_injective (QuotientGroup.mk'_surjective normal)
    rw [htop, Subgroup.comap_top]
  · left
    have hequal : subgroup.comap (QuotientGroup.mk' normal) = normal :=
      (hmaximal.eq_of_le ⟨inferInstance, htop⟩ hcontained).symm
    apply Subgroup.comap_injective (QuotientGroup.mk'_surjective normal)
    rw [hequal]
    ext element
    exact (QuotientGroup.eq_one_iff element).symm

theorem nonsolvable_has_nonabelian_simple_section
    (source : Type u) [Group source] [Finite source]
    (hnonsolvable : ¬ Group.IsSolvable source) :
    ∃ subgroup : Subgroup source, ∃ normal : Subgroup subgroup,
      ∃ hnormal : normal.Normal, letI := hnormal
        IsSimpleGroup (subgroup ⧸ normal) ∧
          ∃ first second : subgroup ⧸ normal, first * second ≠ second * first := by
  have htopNonsolvable : ¬ Group.IsSolvable (⊤ : Subgroup source) := by
    intro hsolvable
    let : Group.IsSolvable (⊤ : Subgroup source) := hsolvable
    let equivalence : (⊤ : Subgroup source) ≃* source := Subgroup.topEquiv
    exact hnonsolvable (Group.isSolvable_of_surjective (f := equivalence.toMonoidHom)
      equivalence.surjective)
  obtain ⟨subgroup, _, hminimal⟩ := Finite.exists_le_minimal
    (p := fun candidate : Subgroup source => ¬ Group.IsSolvable candidate) htopNonsolvable
  have hsubgroupNontrivial : subgroup ≠ ⊥ := by
    intro hbot
    exact hminimal.1 (hbot ▸ inferInstance)
  let : Nontrivial subgroup := subgroup.nontrivial_iff_ne_bot.mpr hsubgroupNontrivial
  obtain ⟨normal, _, hmaximal⟩ := Finite.exists_le_maximal
    (p := fun candidate : Subgroup subgroup => candidate.Normal ∧ candidate ≠ ⊤)
    (a := ⊥) ⟨inferInstance, bot_ne_top⟩
  let : normal.Normal := hmaximal.1.1
  let : IsSimpleGroup (subgroup ⧸ normal) := maximal_normal_quotient_isSimpleGroup normal hmaximal
  have hnormalProper : normal.map subgroup.subtype < subgroup := by
    apply lt_of_le_of_ne (Subgroup.map_subtype_le normal)
    intro hequal
    apply hmaximal.1.2
    apply top_unique
    intro element _
    have hmember : (element : source) ∈ normal.map subgroup.subtype := by
      rw [hequal]
      exact element.property
    obtain ⟨lift, hlift, hequalLift⟩ := hmember
    exact (Subtype.ext hequalLift : lift = element) ▸ hlift
  have hnormalSolvable : Group.IsSolvable (normal.map subgroup.subtype) := by
    by_contra hnonsolvable
    exact hnormalProper.ne (hminimal.eq_of_le hnonsolvable hnormalProper.le)
  let : Group.IsSolvable (normal.map subgroup.subtype) := hnormalSolvable
  let : Group.IsSolvable normal := Group.isSolvable_of_isSolvable_injective
    (f := (normal.equivMapOfInjective subgroup.subtype Subtype.val_injective).toMonoidHom)
    (normal.equivMapOfInjective subgroup.subtype Subtype.val_injective).injective
  have hquotientNonsolvable : ¬ Group.IsSolvable (subgroup ⧸ normal) := by
    intro hsolvable
    exact hminimal.1 ((Group.isSolvable_iff_subgroup_quotient normal).mpr
      ⟨inferInstance, hsolvable⟩)
  have hnonab : ∃ first second : subgroup ⧸ normal, first * second ≠ second * first := by
    by_contra hcommute
    push Not at hcommute
    exact hquotientNonsolvable (Group.isSolvable_of_comm hcommute)
  exact ⟨subgroup, normal, hmaximal.1.1, inferInstance, hnonab⟩

theorem nonsolvable_subgroup_has_ambient_simple_section
    {ambient : Type u} [Group ambient] [Finite ambient]
    (localGroup : Subgroup ambient) (hnonsolvable : ¬ Group.IsSolvable localGroup) :
    ∃ subgroup normal : Subgroup ambient, subgroup ≤ localGroup ∧ normal ≤ subgroup ∧
      ∃ hnormal : (normal.subgroupOf subgroup).Normal, letI := hnormal
        IsSimpleGroup (subgroup ⧸ normal.subgroupOf subgroup) ∧
          ∃ first second : subgroup ⧸ normal.subgroupOf subgroup,
            first * second ≠ second * first := by
  obtain ⟨subgroup, normal, hnormal, hsimple, hnonab⟩ :=
    nonsolvable_has_nonabelian_simple_section localGroup hnonsolvable
  let : normal.Normal := hnormal
  let : IsSimpleGroup (subgroup ⧸ normal) := hsimple
  let ambientSubgroup := subgroup.map localGroup.subtype
  let ambientNormal := (normal.map subgroup.subtype).map localGroup.subtype
  let equivalence : subgroup ≃* ambientSubgroup :=
    subgroup.equivMapOfInjective localGroup.subtype Subtype.val_injective
  let transported := normal.map equivalence.toMonoidHom
  let : transported.Normal := hnormal.map equivalence.toMonoidHom equivalence.surjective
  have hnormalEq : transported = ambientNormal.subgroupOf ambientSubgroup := by
    ext element
    constructor
    · rintro ⟨lift, hlift, rfl⟩
      exact ⟨(lift : localGroup), ⟨lift, hlift, rfl⟩, rfl⟩
    · rintro ⟨outer, ⟨inner, hinner, rfl⟩, hequal⟩
      exact ⟨inner, hinner, Subtype.ext hequal⟩
  have hambientNormal : (ambientNormal.subgroupOf ambientSubgroup).Normal :=
    hnormalEq ▸ (inferInstance : transported.Normal)
  let : (ambientNormal.subgroupOf ambientSubgroup).Normal := hambientNormal
  let quotientEquivalence := QuotientGroup.congr normal
    (ambientNormal.subgroupOf ambientSubgroup) equivalence hnormalEq
  have hambientSimple : IsSimpleGroup (ambientSubgroup ⧸ ambientNormal.subgroupOf ambientSubgroup) :=
    quotientEquivalence.symm.isSimpleGroup
  have hambientNonab : ∃ first second : ambientSubgroup ⧸ ambientNormal.subgroupOf ambientSubgroup,
      first * second ≠ second * first := by
    obtain ⟨first, second, hnotCommute⟩ := hnonab
    refine ⟨quotientEquivalence first, quotientEquivalence second, ?_⟩
    intro hcommute
    apply hnotCommute
    apply quotientEquivalence.injective
    simpa only [map_mul] using hcommute
  refine ⟨ambientSubgroup, ambientNormal, Subgroup.map_subtype_le subgroup, ?_,
    hambientNormal, hambientSimple, hambientNonab⟩
  exact Subgroup.map_mono (Subgroup.map_subtype_le normal)

theorem quotient_subgroup_has_ambient_section_equivalence
    {ambient : Type u} [Group ambient] [Finite ambient]
    (localGroup : Subgroup ambient) (normal : Subgroup localGroup) [normal.Normal]
    (quotientSubgroup : Subgroup (localGroup ⧸ normal)) :
    ∃ subgroup kernel : Subgroup ambient, subgroup ≤ localGroup ∧ kernel ≤ subgroup ∧
      ∃ hnormal : (kernel.subgroupOf subgroup).Normal, letI := hnormal
        Nonempty ((subgroup ⧸ kernel.subgroupOf subgroup) ≃* quotientSubgroup) := by
  let quotientHom := QuotientGroup.mk' normal
  let lifted := quotientSubgroup.comap quotientHom
  let restricted : lifted →* quotientSubgroup :=
    { toFun := fun element => ⟨quotientHom element, element.property⟩
      map_one' := Subtype.ext (map_one quotientHom)
      map_mul' := fun first second =>
        Subtype.ext (map_mul quotientHom (first : localGroup) (second : localGroup)) }
  have hsurjective : Function.Surjective restricted := by
    intro element
    obtain ⟨lift, hlift⟩ := QuotientGroup.mk'_surjective normal element
    have hmember : lift ∈ lifted := by
      change quotientHom lift ∈ quotientSubgroup
      rw [hlift]
      exact element.property
    exact ⟨⟨lift, hmember⟩, Subtype.ext hlift⟩
  let ambientSubgroup := lifted.map localGroup.subtype
  let ambientKernel := (restricted.ker.map lifted.subtype).map localGroup.subtype
  let equivalence : lifted ≃* ambientSubgroup :=
    lifted.equivMapOfInjective localGroup.subtype Subtype.val_injective
  let transported := restricted.ker.map equivalence.toMonoidHom
  let : transported.Normal := (inferInstance : restricted.ker.Normal).map
    equivalence.toMonoidHom equivalence.surjective
  have hkernelEq : transported = ambientKernel.subgroupOf ambientSubgroup := by
    ext element
    constructor
    · rintro ⟨lift, hlift, rfl⟩
      exact ⟨(lift : localGroup), ⟨lift, hlift, rfl⟩, rfl⟩
    · rintro ⟨outer, ⟨inner, hinner, rfl⟩, hequal⟩
      exact ⟨inner, hinner, Subtype.ext hequal⟩
  have hambientNormal : (ambientKernel.subgroupOf ambientSubgroup).Normal :=
    hkernelEq ▸ (inferInstance : transported.Normal)
  let : (ambientKernel.subgroupOf ambientSubgroup).Normal := hambientNormal
  let quotientEquivalence :=
    (QuotientGroup.congr restricted.ker (ambientKernel.subgroupOf ambientSubgroup)
      equivalence hkernelEq).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective restricted hsurjective)
  exact ⟨ambientSubgroup, ambientKernel, Subgroup.map_subtype_le lifted,
    Subgroup.map_mono (Subgroup.map_subtype_le restricted.ker), hambientNormal,
    ⟨quotientEquivalence⟩⟩

theorem kProper_nonsolvable_subgroup_has_known_order_simple_section
    {ambient : Type u} [Group ambient] [Finite ambient]
    (hK : IsKProperByOrder ambient) (localGroup : Subgroup ambient)
    (hproper : localGroup ≠ ⊤) (hnonsolvable : ¬ Group.IsSolvable localGroup) :
    ∃ subgroup normal : Subgroup ambient, subgroup ≤ localGroup ∧ normal ≤ subgroup ∧
      ∃ hnormal : (normal.subgroupOf subgroup).Normal, letI := hnormal
        IsSimpleGroup (subgroup ⧸ normal.subgroupOf subgroup) ∧
          (∃ first second : subgroup ⧸ normal.subgroupOf subgroup,
            first * second ≠ second * first) ∧
          Nat.card (subgroup ⧸ normal.subgroupOf subgroup) ∈ knownSimpleOrders := by
  obtain ⟨subgroup, normal, hcontained, hnormalContained, hnormal, hsimple, hnonab⟩ :=
    nonsolvable_subgroup_has_ambient_simple_section localGroup hnonsolvable
  let : (normal.subgroupOf subgroup).Normal := hnormal
  have hsubgroupProper : subgroup ≠ ⊤ := by
    intro htop
    exact hproper (top_unique (htop ▸ hcontained))
  exact ⟨subgroup, normal, hcontained, hnormalContained, hnormal, hsimple, hnonab,
    hK subgroup normal hsubgroupProper hnormalContained hsimple hnonab⟩

theorem normal_solvable_subgroup_contains_normal_primeSubgroup
    {source : Type u} [Group source] [Finite source]
    (normal : Subgroup source) [normal.Normal] [Group.IsSolvable normal]
    (hnontrivial : normal ≠ ⊥) :
    ∃ prime : ℕ, prime.Prime ∧ ∃ subgroup : Subgroup source,
      subgroup.Normal ∧ subgroup ≠ ⊥ ∧ subgroup ≤ normal ∧ IsPGroup prime subgroup := by
  obtain ⟨subgroup, _, hminimal⟩ := Finite.exists_le_minimal
    (p := fun candidate : Subgroup source => candidate.Normal ∧ candidate ≠ ⊥ ∧ candidate ≤ normal)
    (a := normal) ⟨inferInstance, hnontrivial, le_rfl⟩
  let : subgroup.Normal := hminimal.1.1
  let : Nontrivial subgroup := subgroup.nontrivial_iff_ne_bot.mpr hminimal.1.2.1
  let : Group.IsSolvable subgroup := Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion hminimal.1.2.2) (Subgroup.inclusion_injective hminimal.1.2.2)
  have hcommutatorNormal : ((commutator subgroup).map subgroup.subtype).Normal := inferInstance
  have hcommutatorBot : (commutator subgroup).map subgroup.subtype = ⊥ := by
    by_contra hnontrivial
    have hminimalLe := hminimal.2 ⟨hcommutatorNormal, hnontrivial,
      (Subgroup.map_subtype_le (commutator subgroup)).trans hminimal.1.2.2⟩
      (Subgroup.map_subtype_le (commutator subgroup))
    have htop : commutator subgroup = ⊤ := by
      apply top_unique
      intro element _
      obtain ⟨lift, hlift, hequal⟩ := hminimalLe element.property
      exact (Subtype.ext hequal : lift = element) ▸ hlift
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial subgroup).ne htop
  have hcommutator : commutator subgroup = ⊥ := by
    apply (Subgroup.map_injective (f := subgroup.subtype) Subtype.val_injective)
    simpa only [Subgroup.map_bot] using hcommutatorBot
  let : IsMulCommutative subgroup := (commutator_eq_bot_iff subgroup).mp hcommutator
  obtain ⟨prime, hprime, hdivides⟩ := Nat.exists_prime_and_dvd
    (show Nat.card subgroup ≠ 1 from by
      intro hone
      exact hminimal.1.2.1 (Subgroup.card_eq_one.mp hone))
  let : Fact prime.Prime := ⟨hprime⟩
  let sylow : Sylow prime subgroup := Classical.choice inferInstance
  have hsylowNontrivial : (sylow : Subgroup subgroup) ≠ ⊥ := sylow.ne_bot_of_dvd_card hdivides
  have hsylowNormal : (sylow : Subgroup subgroup).Normal := inferInstance
  let : (sylow : Subgroup subgroup).Characteristic := sylow.characteristic_of_normal hsylowNormal
  have hmapNormal : ((sylow : Subgroup subgroup).map subgroup.subtype).Normal := inferInstance
  have hmapNontrivial : (sylow : Subgroup subgroup).map subgroup.subtype ≠ ⊥ := by
    intro hbot
    apply hsylowNontrivial
    apply (Subgroup.map_injective (f := subgroup.subtype) Subtype.val_injective)
    simpa only [Subgroup.map_bot] using hbot
  have hmapEq : (sylow : Subgroup subgroup).map subgroup.subtype = subgroup :=
    le_antisymm (Subgroup.map_subtype_le _) (hminimal.2 ⟨hmapNormal, hmapNontrivial,
      (Subgroup.map_subtype_le _).trans hminimal.1.2.2⟩
      (Subgroup.map_subtype_le _))
  refine ⟨prime, hprime, subgroup, hminimal.1.1, hminimal.1.2.1, hminimal.1.2.2, ?_⟩
  exact hmapEq ▸ (sylow.isPGroup'.map subgroup.subtype)

theorem solvable_has_nontrivial_normal_primeSubgroup
    (source : Type u) [Group source] [Finite source] [Nontrivial source]
    [Group.IsSolvable source] :
    ∃ prime : ℕ, prime.Prime ∧ ∃ subgroup : Subgroup source,
      subgroup.Normal ∧ subgroup ≠ ⊥ ∧ IsPGroup prime subgroup := by
  obtain ⟨prime, hprime, subgroup, hnormal, hnontrivial, _, hgroup⟩ :=
    normal_solvable_subgroup_contains_normal_primeSubgroup (⊤ : Subgroup source) top_ne_bot
  exact ⟨prime, hprime, subgroup, hnormal, hnontrivial, hgroup⟩

noncomputable abbrev invariant_quotient_mulDistribMulAction
    {acting : Type u} {source : Type v}
    [Group acting] [Group source] [MulDistribMulAction acting source]
    (normal : Subgroup source) [normal.Normal]
    (hinvariant : ∀ scalar : acting, ∀ element ∈ normal, scalar • element ∈ normal) :
    MulDistribMulAction acting (source ⧸ normal) := by
  let : MulAction.QuotientAction acting normal :=
    ⟨fun scalar first second hmember => by
      simpa only [smul_mul', smul_inv'] using hinvariant scalar (first⁻¹ * second) hmember⟩
  exact
    { toMulAction := MulAction.quotient acting normal
      smul_one := fun scalar => by
        change (QuotientGroup.mk' normal) (scalar • 1) = (QuotientGroup.mk' normal) 1
        rw [smul_one]
      smul_mul := fun scalar first second => by
        obtain ⟨firstLift, rfl⟩ := QuotientGroup.mk'_surjective normal first
        obtain ⟨secondLift, rfl⟩ := QuotientGroup.mk'_surjective normal second
        change (QuotientGroup.mk' normal) (scalar • (firstLift * secondLift)) =
          (QuotientGroup.mk' normal) (scalar • firstLift) *
            (QuotientGroup.mk' normal) (scalar • secondLift)
        rw [smul_mul', map_mul] }

theorem normal_coprime_section_le_of_elementary
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup elementary source normal : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (helementary : IsElemAbelian prime elementary)
    (rank : ℕ) (hrank : 3 ≤ rank) (hcard : Nat.card elementary = prime ^ rank)
    (hlargeOrCentral : 4 ≤ rank ∨ elementary ≤ Subgroup.centralizer (normal : Set ambient))
    (helementaryContained : elementary ≤ overgroup)
    (hnormalSource : normal ≤ source) [(normal.subgroupOf source).Normal]
    (hnormalContained : normal ≤ overgroup)
    (hsourceNormalized : elementary ≤ Subgroup.normalizer (source : Set ambient))
    (hnormalNormalized : elementary ≤ Subgroup.normalizer (normal : Set ambient))
    (hquotient : ¬ prime ∣ Nat.card (source ⧸ normal.subgroupOf source)) :
    source ≤ overgroup := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : IsMulCommutative elementary := helementary.1
  let : CommGroup elementary := IsMulCommutative.instCommGroup
  let actionHom : elementary →* MulAut source :=
    source.normalizerMonoidHom.comp (Subgroup.inclusion hsourceNormalized)
  let : MulDistribMulAction elementary source :=
    MulDistribMulAction.compHom source actionHom
  have hinvariant : ∀ scalar : elementary, ∀ element ∈ normal.subgroupOf source,
      scalar • element ∈ normal.subgroupOf source := by
    intro scalar element helement
    change ((scalar • element : source) : ambient) ∈ normal
    change ((source.normalizerMonoidHom
      ⟨scalar, hsourceNormalized scalar.property⟩ element : source) : ambient) ∈ normal
    rw [source.normalizerMonoidHom_apply_apply_coe]
    exact Subgroup.le_normalizer_iff.mp hnormalNormalized scalar scalar.property element helement
  let := invariant_quotient_mulDistribMulAction (acting := elementary)
    (normal.subgroupOf source) hinvariant
  let quotientHom := QuotientGroup.mk' (normal.subgroupOf source)
  let contained := overgroup.subgroupOf source
  have hspans := coprime_group_generated_by_prime_fixedSubgroups
    (acting := elementary) (source := source ⧸ normal.subgroupOf source)
    prime hquotient (fun scalar => by
      apply Subtype.ext
      exact helementary.2 scalar scalar.property)
  have hfixedContained : ∀ fixedGroup : Subgroup (source ⧸ normal.subgroupOf source),
      (∃ kernel : Subgroup elementary,
        (kernel.index = 1 ∨ kernel.index = prime) ∧
          ∀ scalar ∈ kernel, ∀ element ∈ fixedGroup, scalar • element = element) →
      fixedGroup ≤ contained.map quotientHom := by
    rintro fixedGroup ⟨kernel, hindex, hfixed⟩ element helement
    obtain ⟨lift, hlift⟩ := QuotientGroup.mk'_surjective (normal.subgroupOf source) element
    let kernelAmbient := kernel.map elementary.subtype
    let joinGroup := normal ⊔ kernelAmbient
    have hkernelContained : kernelAmbient ≤ overgroup :=
      (Subgroup.map_subtype_le kernel).trans helementaryContained
    have hjoinContained : joinGroup ≤ overgroup := sup_le hnormalContained hkernelContained
    have hjoinRank : rank - 1 ≤ pRank prime joinGroup := by
      exact (elementary_prime_index_subgroup_rank prime hprime helementary rank hcard
        kernel hindex).trans (pRank_mono prime hprime le_sup_right)
    have hliftNormalizes : (lift : ambient) ∈ Subgroup.normalizer (joinGroup : Set ambient) := by
      let ambientJoin : Subgroup ambient := source ⊔ elementary
      let kernelImage := kernelAmbient.subgroupOf ambientJoin
      let normalImage := normal.subgroupOf ambientJoin
      have hnormalJoin : normal ≤ source ⊔ elementary := hnormalSource.trans le_sup_left
      have hjoinNormalizes : source ⊔ elementary ≤ Subgroup.normalizer (normal : Set ambient) :=
        sup_le ((Subgroup.normal_subgroupOf_iff_le_normalizer hnormalSource).mp inferInstance)
          hnormalNormalized
      let : normalImage.Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hnormalJoin).mpr hjoinNormalizes
      let hom := QuotientGroup.mk' normalImage
      have hkernelJoin : kernelAmbient ≤ source ⊔ elementary :=
        (Subgroup.map_subtype_le kernel).trans le_sup_right
      let localLift : ambientJoin := ⟨lift, (show source ≤ source ⊔ elementary from
        le_sup_left) lift.property⟩
      have hlocalCentralizes : hom localLift ∈
          Subgroup.centralizer (kernelImage.map hom : Set (ambientJoin ⧸ normalImage)) := by
        apply Subgroup.mem_centralizer_iff.mpr
        intro member hmember
        obtain ⟨kernelLift, hkernelLift, rfl⟩ := hmember
        obtain ⟨scalar, hscalar, hscalarEq⟩ := hkernelLift
        have hfix := hfixed scalar hscalar element helement
        rw [← hlift] at hfix
        change quotientHom (scalar • lift) = quotientHom lift at hfix
        have hcommutator : ((scalar • lift : source)⁻¹ * lift) ∈ normal.subgroupOf source := by
          apply (QuotientGroup.eq_one_iff _).mp
          change quotientHom ((scalar • lift)⁻¹ * lift) = 1
          rw [map_mul, map_inv, hfix, inv_mul_cancel]
        have hlocalEq : hom ⟨scalar * (lift : ambient) * (scalar : ambient)⁻¹,
            (source ⊔ elementary).mul_mem
              ((source ⊔ elementary).mul_mem
                ((show elementary ≤ source ⊔ elementary from le_sup_right) scalar.property)
                ((show source ≤ source ⊔ elementary from le_sup_left) lift.property))
              ((source ⊔ elementary).inv_mem
                ((show elementary ≤ source ⊔ elementary from le_sup_right) scalar.property))⟩ =
            hom localLift := by
          apply QuotientGroup.eq.mpr
          change ((scalar : ambient) * (lift : ambient) * (scalar : ambient)⁻¹)⁻¹ *
            (lift : ambient) ∈ normal
          change ((scalar • lift : source) : ambient)⁻¹ * (lift : ambient) ∈ normal at hcommutator
          change ((source.normalizerMonoidHom
            ⟨scalar, hsourceNormalized scalar.property⟩ lift : source) : ambient)⁻¹ *
              (lift : ambient) ∈ normal at hcommutator
          simpa only [source.normalizerMonoidHom_apply_apply_coe] using hcommutator
        have hkernelEq : (kernelLift : ambient) = (scalar : ambient) := hscalarEq.symm
        have hconj : hom kernelLift * hom localLift * (hom kernelLift)⁻¹ = hom localLift := by
          rw [← map_inv, ← map_mul, ← map_mul]
          convert hlocalEq using 1
          apply congrArg hom
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, hkernelEq, localLift]
        exact mul_inv_eq_iff_eq_mul.mp hconj
      have hlocalNormalizes : localLift ∈ Subgroup.normalizer
          ((normalImage ⊔ kernelImage : Subgroup ambientJoin) : Set ambientJoin) := by
        rw [← QuotientGroup.comap_map_mk' normalImage kernelImage,
          ← Subgroup.comap_normalizer_eq_of_surjective (kernelImage.map hom)
            (QuotientGroup.mk'_surjective normalImage)]
        exact Subgroup.centralizer_le_normalizer _ hlocalCentralizes
      have hmapJoin : (normalImage ⊔ kernelImage).map (source ⊔ elementary).subtype = joinGroup := by
        rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hnormalJoin,
          Subgroup.map_subgroupOf_eq_of_le hkernelJoin]
      rw [← hmapJoin]
      exact Subgroup.le_normalizer_map (source ⊔ elementary).subtype
        (Subgroup.mem_map_of_mem _ hlocalNormalizes)
    have hliftContained : (lift : ambient) ∈ overgroup := by
      rcases hlargeOrCentral with hlarge | hcentral
      · exact normalizer_le_of_subgroup_rank_in_containing_sylow prime hprime sylow hsylow hcore
          hjoinContained ((show 3 ≤ rank - 1 by omega).trans hjoinRank) hliftNormalizes
      · have hkernelCentral : elementary ≤ Subgroup.centralizer (kernelAmbient : Set ambient) :=
          (Subgroup.le_centralizer_iff_isMulCommutative.mpr helementary.1).trans
            (Subgroup.centralizer_le (Subgroup.map_subtype_le kernel))
        have hjoinCentral : elementary ≤ Subgroup.centralizer (joinGroup : Set ambient) :=
          Subgroup.le_centralizer_iff.mpr (sup_le
            (Subgroup.le_centralizer_iff.mp hcentral)
            (Subgroup.le_centralizer_iff.mp hkernelCentral))
        have hcentralRank : 3 ≤ pRank prime
            (overgroup ⊓ Subgroup.centralizer (joinGroup : Set ambient)) :=
          hrank.trans (le_csSup (pRank_bddAbove prime hprime _)
            ⟨elementary, le_inf helementaryContained hjoinCentral, helementary, hcard⟩)
        exact normalizer_le_of_subgroup_and_centralizer_rank prime hprime sylow hsylow hcore
          hjoinContained ((show 2 ≤ rank - 1 by omega).trans hjoinRank)
          hcentralRank hliftNormalizes
    exact ⟨lift, hliftContained, hlift⟩
  have himageTop : contained.map quotientHom = ⊤ := by
    apply top_unique
    rw [← hspans]
    exact sSup_le hfixedContained
  have hnormalInContained : normal.subgroupOf source ≤ contained := by
    intro element helement
    exact hnormalContained helement
  have hcontainedTop : contained = ⊤ := by
    have hcomap := congrArg (Subgroup.comap quotientHom) himageTop
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hnormalInContained,
      Subgroup.comap_top] at hcomap
    exact hcomap
  intro element helement
  exact (show (⟨element, helement⟩ : source) ∈ contained from hcontainedTop ▸ Subgroup.mem_top _)

theorem normal_coprime_section_le_of_rank_four_elementary
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup elementary source normal : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (helementary : IsElemAbelian prime elementary)
    (rank : ℕ) (hrank : 4 ≤ rank) (hcard : Nat.card elementary = prime ^ rank)
    (helementaryContained : elementary ≤ overgroup)
    (hnormalSource : normal ≤ source) [(normal.subgroupOf source).Normal]
    (hnormalContained : normal ≤ overgroup)
    (hsourceNormalized : elementary ≤ Subgroup.normalizer (source : Set ambient))
    (hnormalNormalized : elementary ≤ Subgroup.normalizer (normal : Set ambient))
    (hquotient : ¬ prime ∣ Nat.card (source ⧸ normal.subgroupOf source)) :
    source ≤ overgroup := by
  exact normal_coprime_section_le_of_elementary prime hprime sylow hsylow hcore
    helementary rank (by omega) hcard (Or.inl hrank) helementaryContained
    hnormalSource hnormalContained hsourceNormalized hnormalNormalized hquotient

theorem normal_coprime_section_le_of_rank_three_centralizing_elementary
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup elementary source normal : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (helementary : IsElemAbelian prime elementary)
    (rank : ℕ) (hrank : 3 ≤ rank) (hcard : Nat.card elementary = prime ^ rank)
    (helementaryContained : elementary ≤ overgroup)
    (hnormalSource : normal ≤ source) [(normal.subgroupOf source).Normal]
    (hnormalContained : normal ≤ overgroup)
    (hsourceNormalized : elementary ≤ Subgroup.normalizer (source : Set ambient))
    (hnormalCentralized : elementary ≤ Subgroup.centralizer (normal : Set ambient))
    (hquotient : ¬ prime ∣ Nat.card (source ⧸ normal.subgroupOf source)) :
    source ≤ overgroup := by
  exact normal_coprime_section_le_of_elementary prime hprime sylow hsylow hcore
    helementary rank hrank hcard (Or.inr hnormalCentralized) helementaryContained
    hnormalSource hnormalContained hsourceNormalized
    (hnormalCentralized.trans (Subgroup.centralizer_le_normalizer _)) hquotient

theorem normal_prime_section_le_of_rank_four_elementary
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime otherPrime : ℕ) (hprime : prime.Prime) (hotherPrime : otherPrime.Prime)
    (hdistinct : prime ≠ otherPrime) (sylow : Sylow prime ambient)
    {overgroup elementary source normal : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (helementary : IsElemAbelian prime elementary)
    (rank : ℕ) (hrank : 4 ≤ rank) (hcard : Nat.card elementary = prime ^ rank)
    (helementaryContained : elementary ≤ overgroup)
    (hnormalSource : normal ≤ source) [(normal.subgroupOf source).Normal]
    (hnormalContained : normal ≤ overgroup)
    (hsourceNormalized : elementary ≤ Subgroup.normalizer (source : Set ambient))
    (hnormalNormalized : elementary ≤ Subgroup.normalizer (normal : Set ambient))
    (hquotient : IsPGroup otherPrime (source ⧸ normal.subgroupOf source)) :
    source ≤ overgroup := by
  let : Fact otherPrime.Prime := ⟨hotherPrime⟩
  have hcoprime : ¬ prime ∣ Nat.card (source ⧸ normal.subgroupOf source) := by
    intro hdivides
    obtain ⟨quotientRank, hquotientCard⟩ := IsPGroup.iff_card.mp hquotient
    exact hdistinct ((Nat.prime_dvd_prime_iff_eq hprime hotherPrime).mp
      (hprime.dvd_of_dvd_pow (hquotientCard ▸ hdivides)))
  exact normal_coprime_section_le_of_rank_four_elementary prime hprime sylow
    hsylow hcore helementary rank hrank hcard helementaryContained hnormalSource
    hnormalContained hsourceNormalized hnormalNormalized hcoprime

theorem intersecting_rank_four_normal_core_quotient_has_no_normal_coprime_subgroup
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup localGroup : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hrank : 4 ≤ pRank prime (localGroup ⊓ overgroup))
    (quotientSubgroup : Subgroup
      (localGroup ⧸ (overgroup.subgroupOf localGroup).normalCore))
    [quotientSubgroup.Normal] (hcoprime : ¬ prime ∣ Nat.card quotientSubgroup) :
    quotientSubgroup = ⊥ := by
  let : Fact prime.Prime := ⟨hprime⟩
  let intersection := overgroup.subgroupOf localGroup
  let normalCore := intersection.normalCore
  let quotientHom := QuotientGroup.mk' normalCore
  let lifted := quotientSubgroup.comap quotientHom
  let : lifted.Normal := inferInstance
  let liftedAmbient := lifted.map localGroup.subtype
  let normalAmbient := normalCore.map localGroup.subtype
  have hnormalLifted : normalCore ≤ lifted := by
    intro element helement
    change quotientHom element ∈ quotientSubgroup
    rw [show quotientHom element = 1 from (QuotientGroup.eq_one_iff element).mpr helement]
    exact quotientSubgroup.one_mem
  have hnormalContained : normalAmbient ≤ overgroup := by
    rintro element ⟨lift, hlift, rfl⟩
    exact intersection.normalCore_le hlift
  have hliftedContained : liftedAmbient ≤ overgroup := by
    obtain ⟨elementary, helementaryContained, helementary, hcard⟩ :=
      pRank_attained prime hprime (localGroup ⊓ overgroup)
    let restricted : lifted →* quotientSubgroup :=
      { toFun := fun element => ⟨quotientHom element, element.property⟩
        map_one' := Subtype.ext (map_one quotientHom)
        map_mul' := fun first second =>
          Subtype.ext (map_mul quotientHom (first : localGroup) (second : localGroup)) }
    have hsurjective : Function.Surjective restricted := by
      intro element
      obtain ⟨lift, hlift⟩ := QuotientGroup.mk'_surjective normalCore element
      have hmember : lift ∈ lifted := by
        change quotientHom lift ∈ quotientSubgroup
        rw [hlift]
        exact element.property
      exact ⟨⟨lift, hmember⟩, Subtype.ext hlift⟩
    have hkernel : restricted.ker = normalCore.subgroupOf lifted := by
      ext element
      change (⟨quotientHom element, element.property⟩ : quotientSubgroup) = 1 ↔
        (element : localGroup) ∈ normalCore
      rw [Subtype.ext_iff]
      exact QuotientGroup.eq_one_iff (N := normalCore) (element : localGroup)
    have hlocalQuotient : ¬ prime ∣ Nat.card (lifted ⧸ normalCore.subgroupOf lifted) := by
      let kernelEquivalence := QuotientGroup.quotientKerEquivOfSurjective restricted hsurjective
      let normalEquivalence := QuotientGroup.congr restricted.ker
        (normalCore.subgroupOf lifted) (MulEquiv.refl lifted)
        (by simpa using hkernel)
      rw [← Nat.card_congr normalEquivalence.toEquiv, Nat.card_congr kernelEquivalence.toEquiv]
      exact hcoprime
    let equivalence : lifted ≃* liftedAmbient :=
      (lifted.equivMapOfInjective localGroup.subtype Subtype.val_injective)
    have hnormalNormalizes : localGroup ≤ Subgroup.normalizer (normalAmbient : Set ambient) := by
      intro element helement
      apply Subgroup.le_normalizer_map localGroup.subtype
      refine ⟨⟨element, helement⟩, ?_, rfl⟩
      change (⟨element, helement⟩ : localGroup) ∈ Subgroup.normalizer (normalCore : Set localGroup)
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top _
    have hnormalSubgroup : (normalAmbient.subgroupOf liftedAmbient).Normal := by
      apply (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_mono hnormalLifted)).mpr
      exact (Subgroup.map_subtype_le lifted).trans hnormalNormalizes
    let : (normalAmbient.subgroupOf liftedAmbient).Normal := hnormalSubgroup
    have hmapNormal : (normalCore.subgroupOf lifted).map equivalence.toMonoidHom =
        normalAmbient.subgroupOf liftedAmbient := by
      ext element
      constructor
      · rintro ⟨lift, hlift, rfl⟩
        exact ⟨(lift : localGroup), hlift, rfl⟩
      · rintro ⟨lift, hlift, hequal⟩
        let liftedElement : lifted := ⟨lift, hnormalLifted hlift⟩
        refine ⟨liftedElement, hlift, ?_⟩
        exact Subtype.ext hequal
    have hquotient : ¬ prime ∣ Nat.card
        (liftedAmbient ⧸ normalAmbient.subgroupOf liftedAmbient) := by
      rw [← Nat.card_congr (QuotientGroup.congr (normalCore.subgroupOf lifted)
        (normalAmbient.subgroupOf liftedAmbient) equivalence hmapNormal).toEquiv]
      exact hlocalQuotient
    have hlocalNormalizes : localGroup ≤ Subgroup.normalizer (liftedAmbient : Set ambient) := by
      intro element helement
      apply Subgroup.le_normalizer_map localGroup.subtype
      refine ⟨⟨element, helement⟩, ?_, rfl⟩
      change (⟨element, helement⟩ : localGroup) ∈ Subgroup.normalizer (lifted : Set localGroup)
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top _
    exact normal_coprime_section_le_of_rank_four_elementary prime hprime
      sylow hsylow hcore helementary (pRank prime (localGroup ⊓ overgroup))
      hrank hcard (helementaryContained.trans inf_le_right)
      (Subgroup.map_mono hnormalLifted) hnormalContained
      ((helementaryContained.trans inf_le_left).trans hlocalNormalizes)
      ((helementaryContained.trans inf_le_left).trans hnormalNormalizes) hquotient
  have hliftedIntersection : lifted ≤ intersection := by
    intro element helement
    exact hliftedContained (Subgroup.mem_map_of_mem localGroup.subtype helement)
  have hliftedCore : lifted ≤ normalCore :=
    Subgroup.normal_le_normalCore.mpr hliftedIntersection
  apply bot_unique
  intro element helement
  obtain ⟨lift, hlift⟩ := QuotientGroup.mk'_surjective normalCore element
  have hliftCore : lift ∈ normalCore := hliftedCore (by
    change quotientHom lift ∈ quotientSubgroup
    rw [hlift]
    exact helement)
  exact Subgroup.mem_bot.mpr (hlift.symm.trans ((QuotientGroup.eq_one_iff lift).mpr hliftCore))

theorem intersecting_rank_four_normal_core_quotient_has_no_normal_primeSubgroup
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup localGroup : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hrank : 4 ≤ pRank prime (localGroup ⊓ overgroup))
    (otherPrime : ℕ) (hotherPrime : otherPrime.Prime)
    (quotientSubgroup : Subgroup
      (localGroup ⧸ (overgroup.subgroupOf localGroup).normalCore))
    [quotientSubgroup.Normal] (hquotientGroup : IsPGroup otherPrime quotientSubgroup) :
    quotientSubgroup = ⊥ := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : Fact otherPrime.Prime := ⟨hotherPrime⟩
  by_cases hequal : prime = otherPrime
  · subst otherPrime
    let intersection := overgroup.subgroupOf localGroup
    let normalCore := intersection.normalCore
    let quotientHom := QuotientGroup.mk' normalCore
    let lifted := quotientSubgroup.comap quotientHom
    let : lifted.Normal := inferInstance
    obtain ⟨localSylow, hlocalSylowContained, _, _⟩ :=
      intersecting_local_has_contained_sylow prime hprime sylow (localGroup := localGroup)
        hsylow hcore (by omega)
    let quotientSylow := Sylow.mapSurjective (QuotientGroup.mk'_surjective normalCore) localSylow
    have hquotientSylow : quotientSubgroup ≤ (quotientSylow : Subgroup (localGroup ⧸ normalCore)) :=
      hquotientGroup.le_sylow_of_normal quotientSylow
    have hliftedLe : lifted ≤ (localSylow : Subgroup localGroup) ⊔ normalCore := by
      have hle := Subgroup.comap_mono (f := quotientHom) hquotientSylow
      rw [Sylow.coe_mapSurjective, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hle
      exact hle
    have hliftedIntersection : lifted ≤ intersection := hliftedLe.trans
      (sup_le (Subgroup.map_le_iff_le_comap.mp hlocalSylowContained) intersection.normalCore_le)
    have hliftedCore : lifted ≤ normalCore :=
      Subgroup.normal_le_normalCore.mpr hliftedIntersection
    apply bot_unique
    intro element helement
    obtain ⟨lift, hlift⟩ := QuotientGroup.mk'_surjective normalCore element
    have hliftCore : lift ∈ normalCore := hliftedCore (by
      change quotientHom lift ∈ quotientSubgroup
      rw [hlift]
      exact helement)
    exact Subgroup.mem_bot.mpr (hlift.symm.trans ((QuotientGroup.eq_one_iff lift).mpr hliftCore))
  · have hcoprime : ¬ prime ∣ Nat.card quotientSubgroup := by
      intro hdivides
      obtain ⟨quotientRank, hquotientCard⟩ := IsPGroup.iff_card.mp hquotientGroup
      exact hequal ((Nat.prime_dvd_prime_iff_eq hprime hotherPrime).mp
        (hprime.dvd_of_dvd_pow (hquotientCard ▸ hdivides)))
    exact intersecting_rank_four_normal_core_quotient_has_no_normal_coprime_subgroup
      prime hprime sylow hsylow hcore hrank quotientSubgroup hcoprime

theorem intersecting_rank_four_normal_core_quotient_has_no_normal_solvable_subgroup
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup localGroup : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hrank : 4 ≤ pRank prime (localGroup ⊓ overgroup))
    (normal : Subgroup (localGroup ⧸ (overgroup.subgroupOf localGroup).normalCore))
    [normal.Normal] [Group.IsSolvable normal] : normal = ⊥ := by
  by_contra hnontrivial
  obtain ⟨otherPrime, hotherPrime, subgroup, hnormal, hnontrivial, _, hgroup⟩ :=
    normal_solvable_subgroup_contains_normal_primeSubgroup normal hnontrivial
  let : subgroup.Normal := hnormal
  exact hnontrivial
    (intersecting_rank_four_normal_core_quotient_has_no_normal_primeSubgroup prime hprime
      sylow hsylow hcore hrank otherPrime hotherPrime subgroup hgroup)

theorem minimal_normal_isPerfect_of_no_normal_solvable_subgroup
    {source : Type u} [Group source] [Finite source]
    (hnoSolvable : ∀ normal : Subgroup source, normal.Normal →
      Group.IsSolvable normal → normal = ⊥)
    (subgroup : Subgroup source)
    (hminimal : Minimal (fun candidate : Subgroup source =>
      candidate.Normal ∧ candidate ≠ ⊥) subgroup) :
    Group.IsPerfect subgroup ∧ Subgroup.center subgroup = ⊥ := by
  let : subgroup.Normal := hminimal.1.1
  have hcommutatorNormal : ((commutator subgroup).map subgroup.subtype).Normal := inferInstance
  have hcommutatorNontrivial : (commutator subgroup).map subgroup.subtype ≠ ⊥ := by
    intro hbot
    have hcommutatorBot : commutator subgroup = ⊥ := by
      apply (Subgroup.map_injective (f := subgroup.subtype) Subtype.val_injective)
      simpa only [Subgroup.map_bot] using hbot
    let : IsMulCommutative subgroup := (commutator_eq_bot_iff subgroup).mp hcommutatorBot
    let : CommGroup subgroup := IsMulCommutative.instCommGroup
    exact hminimal.1.2 (hnoSolvable subgroup inferInstance inferInstance)
  have hcommutatorLe : subgroup ≤ (commutator subgroup).map subgroup.subtype :=
    hminimal.2 ⟨hcommutatorNormal, hcommutatorNontrivial⟩
      (Subgroup.map_subtype_le (commutator subgroup))
  have hperfect : Group.IsPerfect subgroup := Group.isPerfect_def.mpr (by
    apply top_unique
    intro element _
    obtain ⟨lift, hlift, hequal⟩ := hcommutatorLe element.property
    exact (Subtype.ext hequal : lift = element) ▸ hlift)
  have hcenterNormal : ((Subgroup.center subgroup).map subgroup.subtype).Normal := inferInstance
  let : CommGroup (Subgroup.center subgroup) := IsMulCommutative.instCommGroup
  let : Group.IsSolvable ((Subgroup.center subgroup).map subgroup.subtype) :=
    Group.isSolvable_of_surjective
      (f := ((Subgroup.center subgroup).equivMapOfInjective
        subgroup.subtype Subtype.val_injective).toMonoidHom)
      ((Subgroup.center subgroup).equivMapOfInjective subgroup.subtype Subtype.val_injective).surjective
  have hcenterBot := hnoSolvable ((Subgroup.center subgroup).map subgroup.subtype)
    hcenterNormal inferInstance
  refine ⟨hperfect, ?_⟩
  apply (Subgroup.map_injective (f := subgroup.subtype) Subtype.val_injective)
  simpa only [Subgroup.map_bot] using hcenterBot

theorem minimal_normal_map_mulEquiv
    {source : Type u} {target : Type v} [Group source] [Group target]
    (equivalence : source ≃* target) (subgroup : Subgroup source)
    (hminimal : Minimal (fun candidate : Subgroup source =>
      candidate.Normal ∧ candidate ≠ ⊥) subgroup) :
    Minimal (fun candidate : Subgroup target => candidate.Normal ∧ candidate ≠ ⊥)
      (subgroup.map equivalence.toMonoidHom) := by
  have hmapNontrivial : subgroup.map equivalence.toMonoidHom ≠ ⊥ := by
    intro hbot
    apply hminimal.1.2
    apply Subgroup.map_injective (f := equivalence.toMonoidHom) equivalence.injective
    simpa only [Subgroup.map_bot] using hbot
  refine ⟨⟨hminimal.1.1.map equivalence.toMonoidHom equivalence.surjective,
    hmapNontrivial⟩, ?_⟩
  intro candidate hcandidate hcontained
  have hcomapNontrivial : candidate.comap equivalence.toMonoidHom ≠ ⊥ := by
    intro hbot
    have hmap := Subgroup.map_comap_eq_self_of_surjective
      (f := equivalence.toMonoidHom) equivalence.surjective candidate
    rw [hbot, Subgroup.map_bot] at hmap
    exact hcandidate.2 hmap.symm
  have hcomapLe : candidate.comap equivalence.toMonoidHom ≤ subgroup := by
    have hle := Subgroup.comap_mono (f := equivalence.toMonoidHom) hcontained
    rwa [Subgroup.comap_map_eq_self_of_injective equivalence.injective] at hle
  have hminimalLe := hminimal.2
    ⟨hcandidate.1.comap equivalence.toMonoidHom, hcomapNontrivial⟩ hcomapLe
  have hmapLe := Subgroup.map_mono (f := equivalence.toMonoidHom) hminimalLe
  rwa [Subgroup.map_comap_eq_self_of_surjective
    (f := equivalence.toMonoidHom) equivalence.surjective] at hmapLe

theorem distinct_minimal_normal_subgroups_commute
    {source : Type u} [Group source]
    (first second : Subgroup source)
    (hfirst : Minimal (fun candidate : Subgroup source => candidate.Normal ∧ candidate ≠ ⊥) first)
    (hsecond : Minimal (fun candidate : Subgroup source => candidate.Normal ∧ candidate ≠ ⊥) second)
    (hdistinct : first ≠ second) :
    first ≤ Subgroup.centralizer (second : Set source) := by
  let : first.Normal := hfirst.1.1
  let : second.Normal := hsecond.1.1
  have hdisjoint : Disjoint first second := by
    apply disjoint_iff.mpr
    by_contra hnotBot
    have hnontrivial : first ⊓ second ≠ ⊥ := by
      intro hbot
      exact hnotBot hbot
    have hfirstLe := hfirst.2 ⟨inferInstance, hnontrivial⟩ inf_le_left
    have hsecondLe := hsecond.2 ⟨inferInstance, hnontrivial⟩ inf_le_right
    exact hdistinct (le_antisymm (hfirstLe.trans inf_le_right) (hsecondLe.trans inf_le_left))
  intro element helement
  apply Subgroup.mem_centralizer_iff.mpr
  intro other hother
  exact (Subgroup.commute_of_normal_of_disjoint first second hfirst.1.1 hsecond.1.1
    hdisjoint element other helement hother).eq.symm

theorem minimal_normal_subgroup_contains_normal_simple_with_nonab_of_centerless
    {source : Type u} [Group source] [Finite source]
    (subgroup : Subgroup source)
    (hminimal : Minimal (fun candidate : Subgroup source =>
      candidate.Normal ∧ candidate ≠ ⊥) subgroup) :
    ∃ simple : Subgroup subgroup,
      Minimal (fun candidate => candidate.Normal ∧ candidate ≠ ⊥) simple ∧ IsSimpleGroup simple ∧
        (Subgroup.center subgroup = ⊥ → ∃ first second : simple,
          first * second ≠ second * first) ∧
        (∀ prime : ℕ, prime.Prime → prime ∣ Nat.card subgroup → prime ∣ Nat.card simple) := by
  let : subgroup.Normal := hminimal.1.1
  let : Nontrivial subgroup := subgroup.nontrivial_iff_ne_bot.mpr hminimal.1.2
  obtain ⟨simple, _, hsimpleMinimal⟩ := Finite.exists_le_minimal
    (p := fun candidate : Subgroup subgroup => candidate.Normal ∧ candidate ≠ ⊥)
    (a := ⊤) ⟨inferInstance, top_ne_bot⟩
  let : simple.Normal := hsimpleMinimal.1.1
  let : Nontrivial simple := simple.nontrivial_iff_ne_bot.mpr hsimpleMinimal.1.2
  let normalizerHom : source →* Subgroup.normalizer (subgroup : Set source) :=
    { toFun := fun element => ⟨element, by
        rw [Subgroup.normalizer_eq_top]
        exact Subgroup.mem_top _⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }
  let conjugation : source →* MulAut subgroup :=
    subgroup.normalizerMonoidHom.comp normalizerHom
  let conjugate : source → Subgroup subgroup :=
    fun element => simple.map (conjugation element).toMonoidHom
  have hconjugateMinimal : ∀ element, Minimal
      (fun candidate : Subgroup subgroup => candidate.Normal ∧ candidate ≠ ⊥)
      (conjugate element) := fun element =>
    minimal_normal_map_mulEquiv (conjugation element) simple hsimpleMinimal
  let generated := ⨆ element : source, (conjugate element).map subgroup.subtype
  have hgeneratedNormal : generated.Normal := by
    refine ⟨?_⟩
    intro member hmember element
    have hmapLe : generated.map (MulAut.conj element).toMonoidHom ≤ generated := by
      change (⨆ scalar : source, (conjugate scalar).map subgroup.subtype).map
        (MulAut.conj element).toMonoidHom ≤ generated
      rw [Subgroup.map_iSup]
      apply iSup_le
      intro other
      have hmapEq : ((conjugate other).map subgroup.subtype).map
          (MulAut.conj element).toMonoidHom = (conjugate (element * other)).map subgroup.subtype := by
        change ((simple.map (conjugation other).toMonoidHom).map subgroup.subtype).map
          (MulAut.conj element).toMonoidHom =
            (simple.map (conjugation (element * other)).toMonoidHom).map subgroup.subtype
        rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
        congr 1
        ext value
        rw [map_mul]
        change element * (subgroup.subtype ((conjugation other) value)) * element⁻¹ =
          subgroup.subtype ((conjugation element) ((conjugation other) value))
        exact (subgroup.normalizerMonoidHom_apply_apply_coe ⟨element, by
          rw [Subgroup.normalizer_eq_top]
          exact Subgroup.mem_top _⟩ ((conjugation other) value)).symm
      rw [hmapEq]
      exact le_iSup (fun scalar => (conjugate scalar).map subgroup.subtype) (element * other)
    exact hmapLe (Subgroup.mem_map_of_mem (MulAut.conj element).toMonoidHom hmember)
  let : generated.Normal := hgeneratedNormal
  have hgeneratedContained : generated ≤ subgroup := iSup_le fun _ => Subgroup.map_subtype_le _
  have hsimpleGenerated : simple.map subgroup.subtype ≤ generated := by
    have hone : conjugate 1 = simple := by
      change simple.map (conjugation 1).toMonoidHom = simple
      rw [map_one]
      exact Subgroup.map_id simple
    rw [← hone]
    exact le_iSup (fun scalar => (conjugate scalar).map subgroup.subtype) 1
  have hgeneratedNontrivial : generated ≠ ⊥ := by
    intro hbot
    have hsimpleBot : simple.map subgroup.subtype = ⊥ := bot_unique (hbot ▸ hsimpleGenerated)
    apply hsimpleMinimal.1.2
    apply Subgroup.map_injective (f := subgroup.subtype) Subtype.val_injective
    simpa only [Subgroup.map_bot] using hsimpleBot
  have hgeneratedEq : generated = subgroup :=
    le_antisymm hgeneratedContained (hminimal.2 ⟨hgeneratedNormal, hgeneratedNontrivial⟩
      hgeneratedContained)
  have hprimeTransfer : ∀ prime : ℕ, prime.Prime → prime ∣ Nat.card subgroup →
      prime ∣ Nat.card simple := by
    intro prime hprime hdivides
    let factors : Set (Subgroup subgroup) := Set.range conjugate
    let : Fintype factors := Fintype.ofFinite factors
    have hfactorMinimal : ∀ factor : factors, Minimal
        (fun candidate : Subgroup subgroup => candidate.Normal ∧ candidate ≠ ⊥)
        (factor : Subgroup subgroup) := by
      intro factor
      obtain ⟨element, hequal⟩ := factor.property
      exact hequal ▸ hconjugateMinimal element
    have hfactorComm : Pairwise fun first second : factors =>
        ∀ (firstElement : (first : Subgroup subgroup)) (secondElement : (second : Subgroup subgroup)),
          Commute ((first : Subgroup subgroup).subtype firstElement)
            ((second : Subgroup subgroup).subtype secondElement) := by
      intro first second hdistinct firstElement secondElement
      have hne : (first : Subgroup subgroup) ≠ (second : Subgroup subgroup) := by
        intro hequal
        exact hdistinct (Subtype.ext hequal)
      exact (Subgroup.mem_centralizer_iff.mp
        ((distinct_minimal_normal_subgroups_commute (first : Subgroup subgroup)
          (second : Subgroup subgroup)
          (hfactorMinimal first) (hfactorMinimal second) hne) firstElement.property)
          (secondElement : subgroup) secondElement.property).symm
    let productHom := MonoidHom.noncommPiCoprod
      (fun factor : factors => (factor : Subgroup subgroup).subtype) hfactorComm
    have hfamilyAmbient : generated ≤
        (⨆ factor : factors, (factor : Subgroup subgroup)).map subgroup.subtype := by
      apply iSup_le
      intro element
      exact Subgroup.map_mono (le_iSup (fun factor : factors =>
        (factor : Subgroup subgroup)) ⟨conjugate element, ⟨element, rfl⟩⟩)
    have hfamilyTop : (⨆ factor : factors, (factor : Subgroup subgroup)) = ⊤ := by
      apply top_unique
      intro element _
      have hmember : (element : source) ∈ generated := by
        rw [hgeneratedEq]
        exact element.property
      obtain ⟨lift, hlift, hequal⟩ := hfamilyAmbient hmember
      exact (Subtype.ext hequal : lift = element) ▸ hlift
    have hproductTop : productHom.range = ⊤ := by
      rw [MonoidHom.noncommPiCoprod_range]
      simpa only [Subgroup.range_subtype] using hfamilyTop
    have hcardDivides : Nat.card subgroup ∣
        Nat.card ((factor : factors) → (factor : Subgroup subgroup)) := by
      have hrange := Subgroup.card_range_dvd productHom
      rwa [hproductTop, Subgroup.card_top] at hrange
    have hproductDivides := hdivides.trans hcardDivides
    rw [Nat.card_pi] at hproductDivides
    obtain ⟨factor, _, hfactorDivides⟩ :=
      (Prime.dvd_finsetProd_iff hprime.prime _).mp hproductDivides
    obtain ⟨element, hequal⟩ := factor.property
    have hfactorCard : Nat.card (factor : Subgroup subgroup) = Nat.card simple := by
      rw [← hequal]
      exact Subgroup.card_map_of_injective (conjugation element).injective
    exact hfactorCard ▸ hfactorDivides
  have hsimpleGroup : IsSimpleGroup simple := by
    constructor
    intro normal hnormal
    let : normal.Normal := hnormal
    let normalAmbient := normal.map simple.subtype
    have hnormalContained : normalAmbient ≤ simple := Subgroup.map_subtype_le normal
    have hsimpleNormalizes : simple ≤ Subgroup.normalizer (normalAmbient : Set subgroup) := by
      have hnormalEq : normalAmbient.subgroupOf simple = normal :=
        Subgroup.comap_map_eq_self_of_injective Subtype.val_injective normal
      apply (Subgroup.normal_subgroupOf_iff_le_normalizer hnormalContained).mp
      rw [hnormalEq]
      infer_instance
    have hgeneratedNormalizes : generated ≤
        Subgroup.normalizer (normalAmbient.map subgroup.subtype : Set source) := by
      apply iSup_le
      intro element
      have hconjugateNormalizes : conjugate element ≤
          Subgroup.normalizer (normalAmbient : Set subgroup) := by
        by_cases hequal : conjugate element = simple
        · rw [hequal]
          exact hsimpleNormalizes
        · exact ((distinct_minimal_normal_subgroups_commute (conjugate element) simple
            (hconjugateMinimal element) hsimpleMinimal hequal).trans
              (Subgroup.centralizer_le hnormalContained)).trans (Subgroup.centralizer_le_normalizer _)
      exact (Subgroup.map_mono hconjugateNormalizes).trans (by
        intro member hmember
        exact Subgroup.le_normalizer_map subgroup.subtype hmember)
    have hnormalInSubgroup : normalAmbient.Normal := by
      refine ⟨?_⟩
      intro member hmember element
      have hscalar : (element : source) ∈
          Subgroup.normalizer (normalAmbient.map subgroup.subtype : Set source) := by
        apply hgeneratedNormalizes
        rw [hgeneratedEq]
        exact element.property
      have hconjugate := (Subgroup.mem_normalizer_iff.mp hscalar (member : source)).mp
        (Subgroup.mem_map_of_mem subgroup.subtype hmember)
      obtain ⟨lift, hlift, hequal⟩ := hconjugate
      exact (Subtype.ext hequal : lift = element * member * element⁻¹) ▸ hlift
    by_cases hbot : normalAmbient = ⊥
    · left
      apply Subgroup.map_injective (f := simple.subtype) Subtype.val_injective
      simpa only [Subgroup.map_bot] using hbot
    · right
      have hsimpleLe := hsimpleMinimal.2 ⟨hnormalInSubgroup, hbot⟩ hnormalContained
      apply top_unique
      intro element _
      obtain ⟨lift, hlift, hequal⟩ := hsimpleLe element.property
      exact (Subtype.ext hequal : lift = element) ▸ hlift
  refine ⟨simple, hsimpleMinimal, hsimpleGroup, ?_, hprimeTransfer⟩
  intro hcenter
  by_contra hnonab
  have hcommutative : ∀ first second : simple, first * second = second * first := by
    intro first second
    by_contra hnotCommute
    exact hnonab ⟨first, second, hnotCommute⟩
  have hsimpleCentral : simple ≤ Subgroup.centralizer (simple : Set subgroup) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr (IsMulCommutative.of_comm hcommutative)
  have hgeneratedCentral : generated ≤
      Subgroup.centralizer (simple.map subgroup.subtype : Set source) := by
    apply iSup_le
    intro element
    have hconjugateCentral : conjugate element ≤ Subgroup.centralizer (simple : Set subgroup) := by
      by_cases hequal : conjugate element = simple
      · rw [hequal]
        exact hsimpleCentral
      · exact distinct_minimal_normal_subgroups_commute (conjugate element) simple
          (hconjugateMinimal element) hsimpleMinimal hequal
    rintro member ⟨lift, hlift, rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    rintro other ⟨otherLift, hother, rfl⟩
    exact congrArg (fun value : subgroup => (value : source))
      (Subgroup.mem_centralizer_iff.mp (hconjugateCentral hlift) otherLift hother)
  have hsimpleCenter : simple ≤ Subgroup.center subgroup := by
    intro member hmember
    apply Subgroup.mem_center_iff.mpr
    intro element
    have helementCentral : (element : source) ∈
        Subgroup.centralizer (simple.map subgroup.subtype : Set source) := by
      apply hgeneratedCentral
      rw [hgeneratedEq]
      exact element.property
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp helementCentral (member : source)
      (Subgroup.mem_map_of_mem subgroup.subtype hmember)).symm
  exact hsimpleMinimal.1.2 (bot_unique (hcenter ▸ hsimpleCenter))

theorem minimal_normal_subgroup_contains_normal_simple_subgroup
    {source : Type u} [Group source] [Finite source]
    (subgroup : Subgroup source)
    (hminimal : Minimal (fun candidate : Subgroup source =>
      candidate.Normal ∧ candidate ≠ ⊥) subgroup) :
    ∃ simple : Subgroup subgroup,
      Minimal (fun candidate => candidate.Normal ∧ candidate ≠ ⊥) simple ∧ IsSimpleGroup simple := by
  obtain ⟨simple, hsimpleMinimal, hsimpleGroup, _, _⟩ :=
    minimal_normal_subgroup_contains_normal_simple_with_nonab_of_centerless subgroup hminimal
  exact ⟨simple, hsimpleMinimal, hsimpleGroup⟩

theorem centerless_minimal_normal_subgroup_contains_nonabelian_simple_subgroup
    {source : Type u} [Group source] [Finite source]
    (subgroup : Subgroup source)
    (hminimal : Minimal (fun candidate : Subgroup source =>
      candidate.Normal ∧ candidate ≠ ⊥) subgroup)
    (hcenter : Subgroup.center subgroup = ⊥) :
    ∃ simple : Subgroup subgroup,
      Minimal (fun candidate => candidate.Normal ∧ candidate ≠ ⊥) simple ∧
        IsSimpleGroup simple ∧ ∃ first second : simple, first * second ≠ second * first := by
  obtain ⟨simple, hsimpleMinimal, hsimpleGroup, hnonab, _⟩ :=
    minimal_normal_subgroup_contains_normal_simple_with_nonab_of_centerless subgroup hminimal
  exact ⟨simple, hsimpleMinimal, hsimpleGroup, hnonab hcenter⟩

theorem centerless_minimal_normal_subgroup_contains_prime_divisible_nonabelian_simple
    {source : Type u} [Group source] [Finite source]
    (subgroup : Subgroup source)
    (hminimal : Minimal (fun candidate : Subgroup source =>
      candidate.Normal ∧ candidate ≠ ⊥) subgroup)
    (hcenter : Subgroup.center subgroup = ⊥)
    (prime : ℕ) (hprime : prime.Prime) (hdivides : prime ∣ Nat.card subgroup) :
    ∃ simple : Subgroup subgroup,
      Minimal (fun candidate => candidate.Normal ∧ candidate ≠ ⊥) simple ∧
        IsSimpleGroup simple ∧
          (∃ first second : simple, first * second ≠ second * first) ∧ prime ∣ Nat.card simple := by
  obtain ⟨simple, hsimpleMinimal, hsimpleGroup, hnonab, hprimeTransfer⟩ :=
    minimal_normal_subgroup_contains_normal_simple_with_nonab_of_centerless subgroup hminimal
  exact ⟨simple, hsimpleMinimal, hsimpleGroup, hnonab hcenter, hprimeTransfer prime hprime hdivides⟩

theorem escaping_rank_four_quotient_has_perfect_centerless_minimal_normal
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup localGroup : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hrank : 4 ≤ pRank prime (localGroup ⊓ overgroup))
    (hescape : ¬ localGroup ≤ overgroup) :
    ∃ subgroup : Subgroup (localGroup ⧸ (overgroup.subgroupOf localGroup).normalCore),
      Minimal (fun candidate => candidate.Normal ∧ candidate ≠ ⊥) subgroup ∧
        Group.IsPerfect subgroup ∧ Subgroup.center subgroup = ⊥ ∧ prime ∣ Nat.card subgroup := by
  let quotient := localGroup ⧸ (overgroup.subgroupOf localGroup).normalCore
  have hcoreProper : (overgroup.subgroupOf localGroup).normalCore ≠ ⊤ := by
    intro htop
    apply hescape
    intro element helement
    exact (overgroup.subgroupOf localGroup).normalCore_le
      (show (⟨element, helement⟩ : localGroup) ∈
        (overgroup.subgroupOf localGroup).normalCore from htop ▸ Subgroup.mem_top _)
  let : Nontrivial quotient := QuotientGroup.nontrivial_iff.mpr hcoreProper
  obtain ⟨subgroup, _, hminimal⟩ := Finite.exists_le_minimal
    (p := fun candidate : Subgroup quotient => candidate.Normal ∧ candidate ≠ ⊥)
    (a := ⊤) ⟨inferInstance, top_ne_bot⟩
  have hnoSolvable : ∀ normal : Subgroup quotient, normal.Normal →
      Group.IsSolvable normal → normal = ⊥ := by
    intro normal hnormal hsolvable
    let : normal.Normal := hnormal
    let : Group.IsSolvable normal := hsolvable
    exact intersecting_rank_four_normal_core_quotient_has_no_normal_solvable_subgroup
      prime hprime sylow hsylow hcore hrank normal
  obtain ⟨hperfect, hcenter⟩ :=
    minimal_normal_isPerfect_of_no_normal_solvable_subgroup hnoSolvable subgroup hminimal
  refine ⟨subgroup, hminimal, hperfect, hcenter, ?_⟩
  by_contra hcoprime
  let : subgroup.Normal := hminimal.1.1
  exact hminimal.1.2
    (intersecting_rank_four_normal_core_quotient_has_no_normal_coprime_subgroup
      prime hprime sylow hsylow hcore hrank subgroup hcoprime)

theorem escaping_rank_four_quotient_has_prime_divisible_nonabelian_simple_subgroup
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup localGroup : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hrank : 4 ≤ pRank prime (localGroup ⊓ overgroup))
    (hescape : ¬ localGroup ≤ overgroup) :
    ∃ normal : Subgroup (localGroup ⧸ (overgroup.subgroupOf localGroup).normalCore),
      Minimal (fun candidate => candidate.Normal ∧ candidate ≠ ⊥) normal ∧
        ∃ simple : Subgroup normal,
          simple.Normal ∧ IsSimpleGroup simple ∧
            (∃ first second : simple, first * second ≠ second * first) ∧ prime ∣ Nat.card simple := by
  obtain ⟨normal, hminimal, _, hcenter, hdivides⟩ :=
    escaping_rank_four_quotient_has_perfect_centerless_minimal_normal prime hprime sylow
      hsylow hcore hrank hescape
  obtain ⟨simple, hsimpleMinimal, hsimpleGroup, hnonab, hsimpleDivides⟩ :=
    centerless_minimal_normal_subgroup_contains_prime_divisible_nonabelian_simple normal
      hminimal hcenter prime hprime hdivides
  exact ⟨normal, hminimal, simple, hsimpleMinimal.1.1, hsimpleGroup, hnonab, hsimpleDivides⟩

theorem escaping_rank_four_quotient_has_prime_divisible_component
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup localGroup : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hrank : 4 ≤ pRank prime (localGroup ⊓ overgroup))
    (hescape : ¬ localGroup ≤ overgroup) :
    ∃ component : Subgroup (localGroup ⧸ (overgroup.subgroupOf localGroup).normalCore),
      IsComponentOf component ⊤ ∧ IsSimpleGroup component ∧
        (∃ first second : component, first * second ≠ second * first) ∧ prime ∣ Nat.card component := by
  obtain ⟨normal, hminimal, simple, hnormal, hsimple, hnonab, hdivides⟩ :=
    escaping_rank_four_quotient_has_prime_divisible_nonabelian_simple_subgroup
      prime hprime sylow hsylow hcore hrank hescape
  let : normal.Normal := hminimal.1.1
  let : simple.Normal := hnormal
  let : IsSimpleGroup simple := hsimple
  let component := simple.map normal.subtype
  let equivalence : simple ≃* component :=
    simple.equivMapOfInjective normal.subtype Subtype.val_injective
  let : IsSimpleGroup component := equivalence.symm.isSimpleGroup
  have hcomponentNonab : ∃ first second : component, first * second ≠ second * first := by
    obtain ⟨first, second, hnotCommute⟩ := hnonab
    refine ⟨equivalence first, equivalence second, ?_⟩
    intro hcommute
    apply hnotCommute
    apply equivalence.injective
    simpa only [map_mul] using hcommute
  have hcomponentNormal : (component.subgroupOf normal).Normal := by
    have hequal : component.subgroupOf normal = simple :=
      Subgroup.comap_map_eq_self_of_injective Subtype.val_injective simple
    rw [hequal]
    infer_instance
  have hnormalTop : (normal.subgroupOf (⊤ : Subgroup
      (localGroup ⧸ (overgroup.subgroupOf localGroup).normalCore))).Normal := inferInstance
  have hsubnormal : IsSubnormal component ⊤ :=
    IsSubnormal.step (Subgroup.map_subtype_le simple) hcomponentNormal
      (IsSubnormal.step le_top hnormalTop (IsSubnormal.refl ⊤))
  exact ⟨component, ⟨le_top, hsubnormal, nonabelian_simple_isQuasisimple component hcomponentNonab⟩,
    inferInstance, hcomponentNonab,
    (Subgroup.card_map_of_injective (f := normal.subtype) (K := simple)
      Subtype.val_injective) ▸ hdivides⟩

theorem kProper_escaping_rank_four_has_prime_divisible_known_order_simple_section
    {ambient : Type u} [Group ambient] [Finite ambient]
    (hK : IsKProperByOrder ambient) (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup localGroup : Subgroup ambient}
    (hproper : localGroup ≠ ⊤)
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hrank : 4 ≤ pRank prime (localGroup ⊓ overgroup))
    (hescape : ¬ localGroup ≤ overgroup) :
    ∃ subgroup kernel : Subgroup ambient, subgroup ≤ localGroup ∧ kernel ≤ subgroup ∧
      ∃ hnormal : (kernel.subgroupOf subgroup).Normal, letI := hnormal
        IsSimpleGroup (subgroup ⧸ kernel.subgroupOf subgroup) ∧
          (∃ first second : subgroup ⧸ kernel.subgroupOf subgroup,
            first * second ≠ second * first) ∧
          Nat.card (subgroup ⧸ kernel.subgroupOf subgroup) ∈ knownSimpleOrders ∧
          prime ∣ Nat.card (subgroup ⧸ kernel.subgroupOf subgroup) := by
  obtain ⟨normal, _, simple, _, hsimple, hnonab, hdivides⟩ :=
    escaping_rank_four_quotient_has_prime_divisible_nonabelian_simple_subgroup
      prime hprime sylow hsylow hcore hrank hescape
  let simpleImage := simple.map normal.subtype
  let simpleEquivalence : simple ≃* simpleImage :=
    simple.equivMapOfInjective normal.subtype Subtype.val_injective
  obtain ⟨subgroup, kernel, hcontained, hkernelContained, hnormal, ⟨quotientEquivalence⟩⟩ :=
    quotient_subgroup_has_ambient_section_equivalence localGroup
      (overgroup.subgroupOf localGroup).normalCore simpleImage
  let : (kernel.subgroupOf subgroup).Normal := hnormal
  let : IsSimpleGroup simple := hsimple
  let equivalence := quotientEquivalence.trans simpleEquivalence.symm
  have hambientSimple : IsSimpleGroup (subgroup ⧸ kernel.subgroupOf subgroup) :=
    equivalence.isSimpleGroup
  have hambientNonab : ∃ first second : subgroup ⧸ kernel.subgroupOf subgroup,
      first * second ≠ second * first := by
    obtain ⟨first, second, hnotCommute⟩ := hnonab
    refine ⟨equivalence.symm first, equivalence.symm second, ?_⟩
    intro hcommute
    apply hnotCommute
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg equivalence hcommute
  have hsubgroupProper : subgroup ≠ ⊤ := by
    intro htop
    exact hproper (top_unique (htop ▸ hcontained))
  have hquotientCard : Nat.card (subgroup ⧸ kernel.subgroupOf subgroup) = Nat.card simple :=
    Nat.card_congr equivalence.toEquiv
  exact ⟨subgroup, kernel, hcontained, hkernelContained, hnormal, hambientSimple, hambientNonab,
    hK subgroup kernel hsubgroupProper hkernelContained hambientSimple hambientNonab,
    hquotientCard ▸ hdivides⟩

theorem normal_core_solvable_quotient_rank_four_forces_containment
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup localGroup : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    [Group.IsSolvable (localGroup ⧸ (overgroup.subgroupOf localGroup).normalCore)]
    (hrank : 4 ≤ pRank prime (localGroup ⊓ overgroup)) :
    localGroup ≤ overgroup := by
  by_contra hnotContained
  have hnormalCoreProper : (overgroup.subgroupOf localGroup).normalCore ≠ ⊤ := by
    intro htop
    apply hnotContained
    intro element helement
    exact (overgroup.subgroupOf localGroup).normalCore_le
      (show (⟨element, helement⟩ : localGroup) ∈
          (overgroup.subgroupOf localGroup).normalCore from htop ▸ Subgroup.mem_top _)
  let : Nontrivial (localGroup ⧸ (overgroup.subgroupOf localGroup).normalCore) :=
    QuotientGroup.nontrivial_iff.mpr hnormalCoreProper
  obtain ⟨otherPrime, hotherPrime, quotientSubgroup, hnormal, hnontrivial, hgroup⟩ :=
    solvable_has_nontrivial_normal_primeSubgroup
      (localGroup ⧸ (overgroup.subgroupOf localGroup).normalCore)
  let : quotientSubgroup.Normal := hnormal
  exact hnontrivial
    (intersecting_rank_four_normal_core_quotient_has_no_normal_primeSubgroup prime hprime
      sylow hsylow hcore hrank otherPrime hotherPrime quotientSubgroup hgroup)

theorem solvable_intersecting_rank_four_forces_containment
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup localGroup : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    [Group.IsSolvable localGroup]
    (hrank : 4 ≤ pRank prime (localGroup ⊓ overgroup)) :
    localGroup ≤ overgroup :=
  normal_core_solvable_quotient_rank_four_forces_containment prime hprime sylow
    hsylow hcore hrank

theorem solvable_overgroup_eq_weakCore_of_rank_four
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    (overgroup : Subgroup ambient) [Group.IsSolvable overgroup]
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hrank : 4 ≤ pRank prime (sylow : Subgroup ambient)) :
    overgroup = GLBWeakCore prime (sylow : Subgroup ambient) := by
  let weakCore := GLBWeakCore prime (sylow : Subgroup ambient)
  have hsylow : (sylow : Subgroup ambient) ≤ weakCore :=
    subgroup_le_weakCore_of_rank prime hprime (sylow : Subgroup ambient) (by omega)
  have hintersection : 4 ≤ pRank prime (overgroup ⊓ weakCore) :=
    hrank.trans (pRank_mono prime hprime (le_inf (hsylow.trans hcore) hsylow))
  exact le_antisymm
    (solvable_intersecting_rank_four_forces_containment prime hprime sylow hsylow le_rfl hintersection)
    hcore

theorem normal_subgroup_solvable_quotient_rank_four_forces_containment
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup localGroup : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (normal : Subgroup localGroup) [normal.Normal]
    (hnormalContained : normal.map localGroup.subtype ≤ overgroup)
    [Group.IsSolvable (localGroup ⧸ normal)]
    (hrank : 4 ≤ pRank prime (localGroup ⊓ overgroup)) :
    localGroup ≤ overgroup := by
  let normalCore := (overgroup.subgroupOf localGroup).normalCore
  have hnormalCore : normal ≤ normalCore := by
    apply Subgroup.normal_le_normalCore.mpr
    intro element helement
    exact hnormalContained (Subgroup.mem_map_of_mem localGroup.subtype helement)
  let quotientHom := QuotientGroup.lift normal (QuotientGroup.mk' normalCore)
    (by simpa only [QuotientGroup.ker_mk'] using hnormalCore)
  let : Group.IsSolvable (localGroup ⧸ normalCore) :=
    Group.isSolvable_of_surjective (QuotientGroup.lift_surjective_of_surjective normal
      (QuotientGroup.mk' normalCore) (QuotientGroup.mk'_surjective normalCore)
      (by simpa only [QuotientGroup.ker_mk'] using hnormalCore))
  exact normal_core_solvable_quotient_rank_four_forces_containment prime hprime sylow
    hsylow hcore hrank

theorem escaping_intersection_normal_core_rank_le_two
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup localGroup : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hescape : ¬ localGroup ≤ overgroup) :
    pRank prime (overgroup.subgroupOf localGroup).normalCore ≤ 2 := by
  by_contra hnotSmall
  have hnormalContained : (overgroup.subgroupOf localGroup).normalCore.map
      localGroup.subtype ≤ overgroup := by
    rintro element ⟨lift, hlift, rfl⟩
    exact (overgroup.subgroupOf localGroup).normalCore_le hlift
  apply hescape
  apply normal_subgroup_sylow_rank_forces_containment prime hprime sylow hsylow hcore
    (overgroup.subgroupOf localGroup).normalCore hnormalContained
  rw [pRank_map_of_injective prime hprime localGroup.subtype Subtype.val_injective]
  omega

theorem escaping_intersection_quotient_rank_loss_bound
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup localGroup : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hescape : ¬ localGroup ≤ overgroup) :
    pRank prime (localGroup ⊓ overgroup) ≤ 2 +
      pRank prime ((overgroup.subgroupOf localGroup).map
        (QuotientGroup.mk' (overgroup.subgroupOf localGroup).normalCore)) := by
  let normalCore := (overgroup.subgroupOf localGroup).normalCore
  let quotientHom := QuotientGroup.mk' normalCore
  obtain ⟨elementary, hcontained, helementary, hcard⟩ :=
    pRank_attained prime hprime (localGroup ⊓ overgroup)
  have hinside : elementary ≤ localGroup := hcontained.trans inf_le_left
  let lifted := elementary.subgroupOf localGroup
  have hliftedElementary : IsElemAbelian prime lifted := by
    let : IsMulCommutative elementary := helementary.1
    refine ⟨inferInstance, ?_⟩
    intro element helement
    apply Subtype.ext
    exact helementary.2 element helement
  have hliftedCard : Nat.card lifted = prime ^ pRank prime (localGroup ⊓ overgroup) := by
    have hmap := Subgroup.map_subgroupOf_eq_of_le hinside
    rw [← Subgroup.card_map_of_injective (f := localGroup.subtype) Subtype.val_injective,
      hmap, hcard]
  have hbound := elementary_rank_le_kernel_rank_add_image_rank prime hprime quotientHom
    hliftedElementary (pRank prime (localGroup ⊓ overgroup)) hliftedCard
  have hkernelBound : pRank prime quotientHom.ker ≤ 2 := by
    rw [QuotientGroup.ker_mk']
    exact escaping_intersection_normal_core_rank_le_two prime hprime sylow hsylow hcore hescape
  have himageLe : lifted.map quotientHom ≤
      (overgroup.subgroupOf localGroup).map quotientHom := by
    apply Subgroup.map_mono
    intro element helement
    exact (hcontained helement).2
  have himageBound := pRank_mono prime hprime himageLe
  change pRank prime (localGroup ⊓ overgroup) ≤ 2 +
    pRank prime ((overgroup.subgroupOf localGroup).map quotientHom)
  omega

theorem normalized_sup_isSolvable
    {ambient : Type u} [Group ambient]
    (acting source : Subgroup ambient)
    [Group.IsSolvable acting] [Group.IsSolvable source]
    (hnormalized : acting ≤ Subgroup.normalizer (source : Set ambient)) :
    Group.IsSolvable (acting ⊔ source : Subgroup ambient) := by
  let joinGroup : Subgroup ambient := acting ⊔ source
  let normal := source.subgroupOf joinGroup
  let : normal.Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hnormalized
  let equivalence := QuotientGroup.quotientInfEquivProdNormalizerQuotient acting source hnormalized
  let : (source.subgroupOf acting).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnormalized
  let : Group.IsSolvable (joinGroup ⧸ normal) :=
    Group.isSolvable_of_surjective (f := equivalence.toMonoidHom) equivalence.surjective
  let : Group.IsSolvable normal := Group.isSolvable_of_isSolvable_injective
    (f := (source.subgroupOfEquivOfLe (show source ≤ joinGroup from le_sup_right)).toMonoidHom)
    (source.subgroupOfEquivOfLe (show source ≤ joinGroup from le_sup_right)).injective
  exact (Group.isSolvable_iff_subgroup_quotient normal).mpr ⟨inferInstance, inferInstance⟩

theorem elementary_normalized_solvable_subgroup_le
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (sylow : Sylow prime ambient)
    {overgroup elementary source : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (helementary : IsElemAbelian prime elementary)
    (rank : ℕ) (hrank : 4 ≤ rank) (hcard : Nat.card elementary = prime ^ rank)
    (helementaryContained : elementary ≤ overgroup)
    [Group.IsSolvable source]
    (hnormalized : elementary ≤ Subgroup.normalizer (source : Set ambient)) :
    source ≤ overgroup := by
  let : IsMulCommutative elementary := helementary.1
  let : CommGroup elementary := IsMulCommutative.instCommGroup
  let : Group.IsSolvable elementary := inferInstance
  let : Group.IsSolvable (elementary ⊔ source : Subgroup ambient) :=
    normalized_sup_isSolvable elementary source hnormalized
  have hjoinRank : 4 ≤ pRank prime ((elementary ⊔ source : Subgroup ambient) ⊓ overgroup) := by
    exact hrank.trans (le_csSup (pRank_bddAbove prime hprime _)
      ⟨elementary, le_inf le_sup_left helementaryContained, helementary, hcard⟩)
  exact (show source ≤ elementary ⊔ source from le_sup_right).trans
    (solvable_intersecting_rank_four_forces_containment prime hprime sylow hsylow hcore hjoinRank)

end CFSG.PreuniquenessRankFour.Helpers
