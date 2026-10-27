module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.CoprimeAction
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Frattini

public section

open CFSG.Open

namespace CFSG.PreuniquenessRankFour.Helpers

universe u v w

theorem simple_commutative_module_prime_kernel
    {coefficient : Type u} {space : Type v} {acting : Type w}
    [CommRing coefficient] [AddCommGroup space] [Module coefficient space]
    [IsSimpleModule coefficient space] [Group acting] [Finite acting]
    (prime : ℕ) [Fact prime.Prime]
    (hom : acting →* coefficient) (hpow : ∀ scalar : acting, scalar ^ prime = 1) :
    ∃ kernel : Subgroup acting, (kernel.index = 1 ∨ kernel.index = prime) ∧
      ∀ scalar ∈ kernel, ∀ element : space, hom scalar • element = element := by
  obtain ⟨ideal, hideal, ⟨equivalence⟩⟩ := isSimpleModule_iff_quot_maximal.mp
    (inferInstance : IsSimpleModule coefficient space)
  let : ideal.IsMaximal := hideal
  let : Field (coefficient ⧸ ideal) := Ideal.Quotient.field ideal
  let unitHom := ((Ideal.Quotient.mk ideal).toMonoidHom.comp hom).toHomUnits
  let : Finite unitHom.range :=
    Finite.of_surjective unitHom.rangeRestrict unitHom.rangeRestrict_surjective
  have hcard : unitHom.ker.index = Nat.card unitHom.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange unitHom).toEquiv
  let : IsCyclic unitHom.range := inferInstance
  have hcarddivides : Nat.card unitHom.range ∣ prime := by
    rw [← IsCyclic.exponent_eq_card]
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro element
    obtain ⟨scalar, hscalar⟩ := element.property
    apply Subtype.ext
    change element.val ^ prime = 1
    rw [← hscalar, ← map_pow, hpow, map_one]
  refine ⟨unitHom.ker, ?_, ?_⟩
  · rw [hcard]
    exact (Nat.dvd_prime Fact.out).mp hcarddivides
  · intro scalar hscalar element
    apply equivalence.injective
    rw [map_smul]
    have hquotient : (Ideal.Quotient.mk ideal) (hom scalar) = 1 := by
      exact congrArg Units.val hscalar
    change (Ideal.Quotient.mk ideal) (hom scalar) * equivalence element =
      equivalence element
    rw [hquotient, one_mul]

theorem semisimple_commutative_module_prime_fixedSpaces
    {coefficient : Type u} {space : Type v} {acting : Type w}
    [CommRing coefficient] [AddCommGroup space] [Module coefficient space]
    [IsSemisimpleModule coefficient space] [Group acting] [Finite acting]
    (prime : ℕ) [Fact prime.Prime]
    (hom : acting →* coefficient) (hpow : ∀ scalar : acting, scalar ^ prime = 1) :
    sSup {fixedSpace : Submodule coefficient space |
      ∃ kernel : Subgroup acting, (kernel.index = 1 ∨ kernel.index = prime) ∧
        ∀ scalar ∈ kernel, ∀ element ∈ fixedSpace, hom scalar • element = element} = ⊤ := by
  apply top_unique
  rw [← IsSemisimpleModule.sSup_simples_eq_top coefficient space]
  apply sSup_le
  intro simpleSpace hsimple
  let : IsSimpleModule coefficient simpleSpace := hsimple
  obtain ⟨kernel, hindex, hfixed⟩ := simple_commutative_module_prime_kernel
    (space := simpleSpace) prime hom hpow
  apply le_sSup
  refine ⟨kernel, hindex, ?_⟩
  intro scalar hscalar element helement
  exact congrArg Subtype.val (hfixed scalar hscalar ⟨element, helement⟩)

theorem coprime_abelian_representation_prime_fixedSpaces
    {coefficient : Type u} {space : Type v} {acting : Type w}
    [Field coefficient] [AddCommGroup space] [Module coefficient space]
    [CommGroup acting] [Finite acting]
    [NeZero (Nat.card acting : coefficient)]
    (prime : ℕ) [Fact prime.Prime]
    (representation : Representation coefficient acting space)
    (hpow : ∀ scalar : acting, scalar ^ prime = 1) :
    sSup {fixedSpace : Submodule coefficient space |
      ∃ kernel : Subgroup acting, (kernel.index = 1 ∨ kernel.index = prime) ∧
        ∀ scalar ∈ kernel, ∀ element ∈ fixedSpace, representation scalar element = element} =
      ⊤ := by
  let generated := sSup {fixedSpace : Submodule coefficient space |
    ∃ kernel : Subgroup acting, (kernel.index = 1 ∨ kernel.index = prime) ∧
      ∀ scalar ∈ kernel, ∀ element ∈ fixedSpace, representation scalar element = element}
  have hmodule := semisimple_commutative_module_prime_fixedSpaces
    (coefficient := MonoidAlgebra coefficient acting)
    (space := representation.asModule) prime (MonoidAlgebra.of coefficient acting) hpow
  have htop : (⊤ : Submodule coefficient representation.asModule) ≤
      generated.comap representation.asModuleEquiv.toLinearMap := by
    rw [← Submodule.restrictScalars_top coefficient (MonoidAlgebra coefficient acting)
      representation.asModule, ← hmodule, Submodule.restrictScalars_sSup]
    apply sSup_le
    rintro restrictedSpace ⟨fixedSpace, ⟨kernel, hindex, hfixed⟩, rfl⟩
    intro element helement
    change representation.asModuleEquiv element ∈ generated
    have himage : (fixedSpace.restrictScalars coefficient).map
        representation.asModuleEquiv.toLinearMap ∈
        {fixedSpace : Submodule coefficient space |
          ∃ kernel : Subgroup acting, (kernel.index = 1 ∨ kernel.index = prime) ∧
            ∀ scalar ∈ kernel, ∀ element ∈ fixedSpace,
              representation scalar element = element} := by
      refine ⟨kernel, hindex, ?_⟩
      intro scalar hscalar image himage
      obtain ⟨preimage, hpreimage, rfl⟩ := himage
      have hequal := congrArg representation.asModuleEquiv
        (hfixed scalar hscalar preimage hpreimage)
      simpa only [Representation.asModuleEquiv_map_smul,
        Representation.asAlgebraHom_of, LinearEquiv.coe_coe] using hequal
    apply (le_sSup himage)
    exact ⟨element, helement, rfl⟩
  apply top_unique
  intro element helement
  obtain ⟨preimage, rfl⟩ := representation.asModuleEquiv.surjective element
  exact htop (Submodule.mem_top : preimage ∈ (⊤ : Submodule coefficient representation.asModule))

noncomputable def elementary_abelian_action_representation
    {acting : Type u} {source : Type v}
    [Group acting] [CommGroup source] [MulDistribMulAction acting source]
    (prime : ℕ) [Module (ZMod prime) (Additive source)] :
    Representation (ZMod prime) acting (Additive source) :=
  { toFun := fun scalar => AddMonoidHom.toZModLinearMap prime
      (MonoidHom.toAdditive (MulDistribMulAction.toMulAut acting source scalar).toMonoidHom)
    map_one' := by
      ext element
      change Additive.ofMul ((1 : acting) • element.toMul) = element
      rw [one_smul]
      rfl
    map_mul' := by
      intro first second
      ext element
      change Additive.ofMul ((first * second) • element.toMul) =
        Additive.ofMul (first • (second • element.toMul))
      rw [mul_smul] }

theorem elementary_abelian_group_prime_fixedSubgroups
    {acting : Type u} {source : Type v}
    [CommGroup acting] [Finite acting] [CommGroup source]
    [MulDistribMulAction acting source]
    (actingPrime sourcePrime : ℕ) [Fact actingPrime.Prime] [Fact sourcePrime.Prime]
    [Module (ZMod sourcePrime) (Additive source)]
    [NeZero (Nat.card acting : ZMod sourcePrime)]
    (hpow : ∀ scalar : acting, scalar ^ actingPrime = 1) :
    sSup {fixedGroup : Subgroup source |
      ∃ kernel : Subgroup acting, (kernel.index = 1 ∨ kernel.index = actingPrime) ∧
        ∀ scalar ∈ kernel, ∀ element ∈ fixedGroup, scalar • element = element} = ⊤ := by
  let representation := elementary_abelian_action_representation
    (acting := acting) (source := source) sourcePrime
  let generated := sSup {fixedGroup : Subgroup source |
    ∃ kernel : Subgroup acting, (kernel.index = 1 ∨ kernel.index = actingPrime) ∧
      ∀ scalar ∈ kernel, ∀ element ∈ fixedGroup, scalar • element = element}
  let generatedSpace := AddSubgroup.toZModSubmodule sourcePrime
    (Subgroup.toAddSubgroup generated)
  have hspans := coprime_abelian_representation_prime_fixedSpaces
    actingPrime representation hpow
  have htop : (⊤ : Submodule (ZMod sourcePrime) (Additive source)) ≤ generatedSpace := by
    rw [← hspans]
    apply sSup_le
    rintro fixedSpace ⟨kernel, hindex, hfixed⟩
    intro element helement
    change element.toMul ∈ generated
    have hfixedGroup : Subgroup.toAddSubgroup.symm fixedSpace.toAddSubgroup ∈
        {fixedGroup : Subgroup source |
          ∃ kernel : Subgroup acting, (kernel.index = 1 ∨ kernel.index = actingPrime) ∧
            ∀ scalar ∈ kernel, ∀ element ∈ fixedGroup, scalar • element = element} := by
      refine ⟨kernel, hindex, ?_⟩
      intro scalar hscalar fixedElement hmem
      exact congrArg Additive.toMul (hfixed scalar hscalar (Additive.ofMul fixedElement) hmem)
    exact (le_sSup hfixedGroup) helement
  apply top_unique
  intro element helement
  exact htop (Submodule.mem_top : Additive.ofMul element ∈
    (⊤ : Submodule (ZMod sourcePrime) (Additive source)))

theorem coprime_pGroup_generated_by_prime_fixedSubgroups
    {acting : Type u} {source : Type v}
    [CommGroup acting] [Finite acting] [Group source] [Finite source]
    [MulDistribMulAction acting source]
    (actingPrime sourcePrime : ℕ) [Fact actingPrime.Prime] [Fact sourcePrime.Prime]
    (hdistinct : actingPrime ≠ sourcePrime) (hgroup : IsPGroup sourcePrime source)
    (hpow : ∀ scalar : acting, scalar ^ actingPrime = 1) :
    sSup {fixedGroup : Subgroup source |
      ∃ kernel : Subgroup acting, (kernel.index = 1 ∨ kernel.index = actingPrime) ∧
        ∀ scalar ∈ kernel, ∀ element ∈ fixedGroup, scalar • element = element} = ⊤ := by
  let generated := sSup {fixedGroup : Subgroup source |
    ∃ kernel : Subgroup acting, (kernel.index = 1 ∨ kernel.index = actingPrime) ∧
      ∀ scalar ∈ kernel, ∀ element ∈ fixedGroup, scalar • element = element}
  let : IsMulCommutative (source ⧸ frattini source) :=
    pGroup_frattini_quotient_isMulCommutative sourcePrime hgroup
  let : CommGroup (source ⧸ frattini source) := IsMulCommutative.instCommGroup
  let : Module (ZMod sourcePrime) (Additive (source ⧸ frattini source)) :=
    AddCommGroup.zmodModule fun element => by
      change Additive.ofMul (element.toMul ^ sourcePrime) = 0
      rw [pGroup_frattini_quotient_pow_eq_one sourcePrime hgroup]
      rfl
  let := characteristic_quotient_mulDistribMulAction (acting := acting) (frattini source)
  have hacting : IsPGroup actingPrime acting := isPGroup_iff_pow_pow_eq_one.mpr
    fun scalar => ⟨1, by simpa only [pow_one] using hpow scalar⟩
  let : NeZero (Nat.card acting : ZMod sourcePrime) := by
    constructor
    intro hzero
    have hdivides := (ZMod.natCast_eq_zero_iff (Nat.card acting) sourcePrime).mp hzero
    obtain ⟨rank, hcard⟩ := IsPGroup.iff_card.mp hacting
    have hcoprime : sourcePrime.Coprime (Nat.card acting) := by
      rw [hcard]
      simpa only [pow_one] using Nat.coprime_pow_primes 1 rank
        (Fact.out : sourcePrime.Prime) (Fact.out : actingPrime.Prime) hdistinct.symm
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : sourcePrime.Prime)).mp hcoprime hdivides
  have hcoprime : ¬ actingPrime ∣ Nat.card (frattini source) := by
    obtain ⟨rank, hcard⟩ := IsPGroup.iff_card.mp (hgroup.to_subgroup (frattini source))
    apply (Nat.Prime.coprime_iff_not_dvd (Fact.out : actingPrime.Prime)).mp
    rw [hcard]
    simpa only [pow_one] using Nat.coprime_pow_primes 1 rank
      (Fact.out : actingPrime.Prime) (Fact.out : sourcePrime.Prime) hdistinct
  have hspans := elementary_abelian_group_prime_fixedSubgroups
    (source := source ⧸ frattini source) actingPrime sourcePrime hpow
  have hquotient : (⊤ : Subgroup (source ⧸ frattini source)) ≤
      generated.map (QuotientGroup.mk' (frattini source)) := by
    rw [← hspans]
    apply sSup_le
    rintro fixedGroup ⟨kernel, hindex, hfixed⟩
    intro element helement
    let : MulAction kernel source := MulAction.compHom source kernel.subtype
    let : MulAction kernel (source ⧸ frattini source) :=
      MulAction.compHom (source ⧸ frattini source) kernel.subtype
    obtain ⟨lift, hequal, hlift⟩ := fixedPoint_lifts_of_prime_coprime_kernel
      actingPrime (hacting.to_subgroup kernel) (QuotientGroup.mk' (frattini source))
      (QuotientGroup.mk'_surjective (frattini source))
      (fun scalar sourceElement => rfl)
      (by simpa only [QuotientGroup.ker_mk'] using hcoprime) element
      (fun scalar => hfixed scalar.val scalar.property element helement)
    let : MulDistribMulAction kernel source :=
      MulDistribMulAction.compHom source kernel.subtype
    have hliftmem : lift ∈ generated := by
      apply Subgroup.mem_sSup_of_mem (s := FixedPoints.subgroup kernel source)
      · refine ⟨kernel, hindex, ?_⟩
        intro scalar hscalar fixedElement hmem
        exact hmem ⟨scalar, hscalar⟩
      · exact hlift
    exact ⟨lift, hliftmem, hequal⟩
  have hmaptop : generated.map (QuotientGroup.mk' (frattini source)) = ⊤ :=
    top_unique hquotient
  have hgenerates : generated ⊔ frattini source = ⊤ := by
    rw [← QuotientGroup.ker_mk' (frattini source), ← Subgroup.comap_map_eq, hmaptop]
    exact Subgroup.comap_top _
  exact frattini_nongenerating hgenerates

open scoped Pointwise in
theorem coprime_group_generated_by_prime_fixedSubgroups
    {acting : Type u} {source : Type v}
    [CommGroup acting] [Finite acting] [Group source] [Finite source]
    [MulDistribMulAction acting source]
    (actingPrime : ℕ) [Fact actingPrime.Prime]
    (hcoprime : ¬ actingPrime ∣ Nat.card source)
    (hpow : ∀ scalar : acting, scalar ^ actingPrime = 1) :
    sSup {fixedGroup : Subgroup source |
      ∃ kernel : Subgroup acting, (kernel.index = 1 ∨ kernel.index = actingPrime) ∧
        ∀ scalar ∈ kernel, ∀ element ∈ fixedGroup, scalar • element = element} = ⊤ := by
  let generated := sSup {fixedGroup : Subgroup source |
    ∃ kernel : Subgroup acting, (kernel.index = 1 ∨ kernel.index = actingPrime) ∧
      ∀ scalar ∈ kernel, ∀ element ∈ fixedGroup, scalar • element = element}
  have hacting : IsPGroup actingPrime acting := isPGroup_iff_pow_pow_eq_one.mpr
    fun scalar => ⟨1, by simpa only [pow_one] using hpow scalar⟩
  have hsylows : ∀ sourcePrime : ℕ, sourcePrime.Prime →
      ∃ sourceSylow : Sylow sourcePrime source, (sourceSylow : Subgroup source) ≤ generated := by
    intro sourcePrime hsourcePrime
    let : Fact sourcePrime.Prime := ⟨hsourcePrime⟩
    have hcard : ¬ actingPrime ∣ Nat.card (Sylow sourcePrime source) := by
      intro hdivides
      let sourceSylow : Sylow sourcePrime source := Classical.choice inferInstance
      exact hcoprime (hdivides.trans
        (sourceSylow.card_dvd_index.trans (sourceSylow : Subgroup source).index_dvd_card))
    obtain ⟨sourceSylow, hfixed⟩ :=
      hacting.nonempty_fixed_point_of_prime_not_dvd_card (Sylow sourcePrime source) hcard
    refine ⟨sourceSylow, ?_⟩
    by_cases hequal : actingPrime = sourcePrime
    · have hcardOne : Nat.card (sourceSylow : Subgroup source) = 1 := by
        apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
        intro divisor hdivisor hdivides
        obtain ⟨sourceRank, hcardSource⟩ := IsPGroup.iff_card.mp sourceSylow.isPGroup'
        have hsame : divisor = sourcePrime :=
          (Nat.prime_dvd_prime_iff_eq hdivisor hsourcePrime).mp
            (hdivisor.dvd_of_dvd_pow (hcardSource ▸ hdivides))
        exact hcoprime (hequal ▸ hsame ▸
          hdivides.trans (sourceSylow : Subgroup source).card_subgroup_dvd_card)
      exact (Subgroup.card_eq_one.mp hcardOne) ▸ bot_le
    · have hstable : ∀ scalar : acting, ∀ element ∈ (sourceSylow : Subgroup source),
          scalar • element ∈ (sourceSylow : Subgroup source) := by
        intro scalar element helement
        have hmap : scalar • (sourceSylow : Subgroup source) =
            (sourceSylow : Subgroup source) := by
          rw [← Sylow.pointwise_smul_def, hfixed scalar]
        rw [← hmap, Subgroup.pointwise_smul_def]
        exact Subgroup.mem_map_of_mem _ helement
      let : MulDistribMulAction acting (sourceSylow : Subgroup source) :=
        { smul := fun scalar element => ⟨scalar • (element : source),
            hstable scalar element element.property⟩
          one_smul := fun element => Subtype.ext (one_smul acting (element : source))
          mul_smul := fun first second element =>
            Subtype.ext (mul_smul first second (element : source))
          smul_one := fun scalar => Subtype.ext (smul_one scalar)
          smul_mul := fun scalar first second =>
            Subtype.ext (smul_mul' scalar (first : source) (second : source)) }
      have hspans := coprime_pGroup_generated_by_prime_fixedSubgroups
        (acting := acting) actingPrime sourcePrime hequal sourceSylow.isPGroup' hpow
      have hcontained : (⊤ : Subgroup (sourceSylow : Subgroup source)) ≤
          generated.comap (sourceSylow : Subgroup source).subtype := by
        rw [← hspans]
        apply sSup_le
        rintro fixedGroup ⟨kernel, hindex, hfixedGroup⟩
        apply Subgroup.map_le_iff_le_comap.mp
        apply le_sSup
        refine ⟨kernel, hindex, ?_⟩
        rintro scalar hscalar element ⟨lift, hlift, rfl⟩
        exact congrArg Subtype.val (hfixedGroup scalar hscalar lift hlift)
      intro element helement
      exact hcontained (Subgroup.mem_top (⟨element, helement⟩ :
        (sourceSylow : Subgroup source)))
  have hindex : generated.index = 1 := by
    apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
    intro sourcePrime hsourcePrime hdivides
    let : Fact sourcePrime.Prime := ⟨hsourcePrime⟩
    obtain ⟨sourceSylow, hcontained⟩ := hsylows sourcePrime hsourcePrime
    exact sourceSylow.not_dvd_index (hdivides.trans (Subgroup.index_dvd_of_le hcontained))
  exact Subgroup.index_eq_one.mp hindex

theorem elementary_prime_index_subgroup_rank
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) {elementary : Subgroup ambient}
    (helementary : IsElemAbelian prime elementary)
    (rank : ℕ) (hcard : Nat.card elementary = prime ^ rank)
    (kernel : Subgroup elementary) (hindex : kernel.index = 1 ∨ kernel.index = prime) :
    rank - 1 ≤ pRank prime (kernel.map elementary.subtype) := by
  let : Fact prime.Prime := ⟨hprime⟩
  have hgroup : IsPGroup prime elementary := IsPGroup.of_card hcard
  obtain ⟨kernelRank, hkernelCard⟩ := IsPGroup.iff_card.mp (hgroup.to_subgroup kernel)
  have hkernelRank : rank - 1 ≤ kernelRank := by
    have hproduct := kernel.card_mul_index
    rw [hkernelCard, hcard] at hproduct
    rcases hindex with hindex | hindex
    · rw [hindex, mul_one] at hproduct
      have hequal := Nat.pow_right_injective hprime.two_le hproduct
      omega
    · rw [hindex, ← pow_succ] at hproduct
      have hequal := Nat.pow_right_injective hprime.two_le hproduct
      omega
  apply hkernelRank.trans
  apply le_csSup (pRank_bddAbove prime hprime (kernel.map elementary.subtype))
  refine ⟨kernel.map elementary.subtype, le_rfl, ?_, ?_⟩
  · let : IsMulCommutative elementary := helementary.1
    refine ⟨isMulCommutative_iff.mpr ?_, ?_⟩
    · intro first second
      apply Subtype.ext
      exact congrArg (fun value : elementary => (value : ambient))
        ((isMulCommutative_iff.mp helementary.1)
        (⟨first.val, Subgroup.map_subtype_le kernel first.property⟩ : elementary)
        (⟨second.val, Subgroup.map_subtype_le kernel second.property⟩ : elementary))
    intro element helement
    exact helementary.2 element (Subgroup.map_subtype_le kernel helement)
  · rw [Subgroup.card_map_of_injective elementary.subtype_injective, hkernelCard]

theorem elementary_normalized_primeSubgroup_le_weakCore
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime sourcePrime : ℕ) (hprime : prime.Prime) (hsourcePrime : sourcePrime.Prime)
    (hdistinct : prime ≠ sourcePrime)
    {elementary sylowGroup twoGroup : Subgroup ambient}
    (helementary : IsElemAbelian prime elementary)
    (rank : ℕ) (hrank : 3 ≤ rank) (hcard : Nat.card elementary = prime ^ rank)
    (hcontained : elementary ≤ sylowGroup) (htwo : IsPGroup sourcePrime twoGroup)
    (hnormalized : elementary ≤ Subgroup.normalizer (twoGroup : Set ambient)) :
    twoGroup ≤ GLBWeakCore prime sylowGroup := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : Fact sourcePrime.Prime := ⟨hsourcePrime⟩
  let : IsMulCommutative elementary := helementary.1
  let : CommGroup elementary := IsMulCommutative.instCommGroup
  let actionHom := twoGroup.normalizerMonoidHom.comp (Subgroup.inclusion hnormalized)
  let := MulDistribMulAction.compHom twoGroup actionHom
  have hpow : ∀ scalar : elementary, scalar ^ prime = 1 := by
    intro scalar
    apply Subtype.ext
    exact helementary.2 scalar.val scalar.property
  have hgenerated := coprime_pGroup_generated_by_prime_fixedSubgroups
    prime sourcePrime hdistinct htwo hpow
  have htop : (⊤ : Subgroup twoGroup) ≤
      (GLBWeakCore prime sylowGroup).comap twoGroup.subtype := by
    rw [← hgenerated]
    apply sSup_le
    rintro fixedGroup ⟨kernel, hindex, hfixed⟩
    have hkernelRank := elementary_prime_index_subgroup_rank prime hprime
      helementary rank hcard kernel hindex
    have hkernelTwo : 2 ≤ pRank prime (kernel.map elementary.subtype) :=
      (show 2 ≤ rank - 1 by omega).trans hkernelRank
    have helementaryRank : 3 ≤ pRank prime elementary := by
      apply hrank.trans
      apply le_csSup (pRank_bddAbove prime hprime elementary)
      exact ⟨elementary, le_rfl, helementary, hcard⟩
    have hkernelCore : Subgroup.normalizer (kernel.map elementary.subtype : Set ambient) ≤
        GLBWeakCore prime sylowGroup :=
      normalizer_le_weakCore_of_commutative_overgroup prime hprime hcontained
        (Subgroup.map_subtype_le kernel) helementary.1 hkernelTwo helementaryRank
    intro element helement
    apply hkernelCore
    apply Subgroup.centralizer_le_normalizer
    apply Subgroup.mem_centralizer_iff.mpr
    intro kernelElement hkernelElement
    obtain ⟨scalar, hscalar, rfl⟩ := hkernelElement
    have hequal := congrArg Subtype.val (hfixed scalar hscalar element helement)
    change (scalar : ambient) * (element : ambient) * (scalar : ambient)⁻¹ = element at hequal
    have hcommute := mul_inv_eq_iff_eq_mul.mp hequal
    exact hcommute
  intro element helement
  exact htop (Subgroup.mem_top (⟨element, helement⟩ : twoGroup))

theorem elementary_normalized_twoSubgroup_le_weakCore
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    {elementary sylowGroup twoGroup : Subgroup ambient}
    (helementary : IsElemAbelian prime elementary)
    (rank : ℕ) (hrank : 3 ≤ rank) (hcard : Nat.card elementary = prime ^ rank)
    (hcontained : elementary ≤ sylowGroup) (htwo : IsPGroup 2 twoGroup)
    (hnormalized : elementary ≤ Subgroup.normalizer (twoGroup : Set ambient)) :
    twoGroup ≤ GLBWeakCore prime sylowGroup := by
  exact elementary_normalized_primeSubgroup_le_weakCore prime 2 hprime (by norm_num)
    hodd helementary rank hrank hcard hcontained htwo hnormalized

end CFSG.PreuniquenessRankFour.Helpers
