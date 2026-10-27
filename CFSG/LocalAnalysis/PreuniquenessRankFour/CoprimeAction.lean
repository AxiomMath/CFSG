module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers

public section

open CFSG.Open
open CFSG.Open
open scoped Pointwise

namespace CFSG.PreuniquenessRankFour.Helpers

universe u v w

theorem fixedPoint_lifts_of_prime_coprime_kernel
    {acting : Type u} {source : Type v} {target : Type w}
    [Group acting] [Group source] [Group target]
    [MulAction acting source] [MulAction acting target]
    (prime : ℕ) [Fact prime.Prime] (hacting : IsPGroup prime acting)
    (hom : source →* target) (hsurjective : Function.Surjective hom)
    (hequivariant : ∀ (scalar : acting) (element : source),
      hom (scalar • element) = scalar • hom element)
    (hcoprime : ¬ prime ∣ Nat.card hom.ker)
    (element : target) (hfixed : ∀ scalar : acting, scalar • element = element) :
    ∃ lift : source, hom lift = element ∧ ∀ scalar : acting, scalar • lift = lift := by
  let fiber := {lift : source // hom lift = element}
  let : MulAction acting fiber :=
    { smul := fun scalar lift =>
        ⟨scalar • lift.val, by rw [hequivariant, lift.property, hfixed]⟩
      one_smul := fun lift => Subtype.ext (one_smul acting lift.val)
      mul_smul := fun first second lift => Subtype.ext (mul_smul first second lift.val) }
  have hcard : Nat.card fiber = Nat.card hom.ker :=
    Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective hsurjective element)
  obtain ⟨lift, hlift⟩ := hacting.nonempty_fixed_point_of_prime_not_dvd_card fiber
    (hcard ▸ hcoprime)
  refine ⟨lift.val, lift.property, ?_⟩
  intro scalar
  exact congrArg Subtype.val (hlift scalar)

theorem fixed_transporter_of_coprime_pGroup
    {acting : Type u} {source : Type v} {space : Type w}
    [Group acting] [Group source] [Finite source]
    [MulDistribMulAction acting source] [MulAction source space] [MulAction acting space]
    (prime : ℕ) [Fact prime.Prime] (hacting : IsPGroup prime acting)
    (hcoprime : ¬ prime ∣ Nat.card source)
    (hequivariant : ∀ (scalar : acting) (element : source) (point : space),
      scalar • (element • point) = (scalar • element) • (scalar • point))
    (first second : space) (hfirst : ∀ scalar : acting, scalar • first = first)
    (hsecond : ∀ scalar : acting, scalar • second = second)
    (hconjugate : ∃ element : source, element • first = second) :
    ∃ element : source, element • first = second ∧
      ∀ scalar : acting, scalar • element = element := by
  let transporter := {element : source // element • first = second}
  let : MulAction acting transporter :=
    { smul := fun scalar element =>
        ⟨scalar • element.val, by
          have hequal := hequivariant scalar element.val first
          rw [element.property, hfirst, hsecond] at hequal
          exact hequal.symm⟩
      one_smul := fun element => Subtype.ext (one_smul acting element.val)
      mul_smul := fun firstScalar secondScalar element =>
        Subtype.ext (mul_smul firstScalar secondScalar element.val) }
  obtain ⟨conjugator, hconjugator⟩ := hconjugate
  let equivalence : MulAction.stabilizer source first ≃ transporter :=
    { toFun := fun element => ⟨conjugator * element.val, by
        rw [mul_smul, MulAction.mem_stabilizer_iff.mp element.property, hconjugator]⟩
      invFun := fun element => ⟨conjugator⁻¹ * element.val, by
        apply MulAction.mem_stabilizer_iff.mpr
        rw [mul_smul, element.property, ← hconjugator, inv_smul_smul]⟩
      left_inv := fun element => Subtype.ext (inv_mul_cancel_left conjugator element.val)
      right_inv := fun element => Subtype.ext (mul_inv_cancel_left conjugator element.val) }
  have hcard : ¬ prime ∣ Nat.card transporter := by
    rw [← Nat.card_congr equivalence]
    intro hdivides
    exact hcoprime (hdivides.trans
      (MulAction.stabilizer source first).card_subgroup_dvd_card)
  obtain ⟨element, hfixed⟩ :=
    hacting.nonempty_fixed_point_of_prime_not_dvd_card transporter hcard
  exact ⟨element.val, element.property,
    fun scalar => congrArg Subtype.val (hfixed scalar)⟩

theorem invariant_sylows_conjugate_by_fixed_element
    {acting : Type u} {source : Type v}
    [Group acting] [Group source] [Finite source] [MulDistribMulAction acting source]
    (actingPrime sourcePrime : ℕ) [Fact actingPrime.Prime] [Fact sourcePrime.Prime]
    (hacting : IsPGroup actingPrime acting) (hcoprime : ¬ actingPrime ∣ Nat.card source)
    (first second : Sylow sourcePrime source)
    (hfirst : ∀ scalar : acting, scalar • first = first)
    (hsecond : ∀ scalar : acting, scalar • second = second) :
    ∃ element : source, element • first = second ∧
      ∀ scalar : acting, scalar • element = element := by
  apply fixed_transporter_of_coprime_pGroup actingPrime hacting hcoprime
    (first := first) (second := second)
  · intro scalar element sylow
    apply Sylow.ext
    rw [Sylow.pointwise_smul_def, Sylow.coe_subgroup_smul,
      Sylow.coe_subgroup_smul, Sylow.pointwise_smul_def]
    rw [Subgroup.pointwise_smul_def, Subgroup.pointwise_smul_def,
      Subgroup.pointwise_smul_def, Subgroup.pointwise_smul_def]
    change ((sylow : Subgroup source).map (MulAut.conj element).toMonoidHom).map
      (MulDistribMulAction.toMulAut acting source scalar).toMonoidHom =
      ((sylow : Subgroup source).map
        (MulDistribMulAction.toMulAut acting source scalar).toMonoidHom).map
          (MulAut.conj (scalar • element)).toMonoidHom
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext member
    change scalar • (element * member * element⁻¹) =
      (scalar • element) * (scalar • member) * (scalar • element)⁻¹
    rw [smul_mul', smul_mul', smul_inv']
  · exact hfirst
  · exact hsecond
  · exact MulAction.exists_smul_eq source first second

theorem characteristic_subgroup_quotientAction
    {acting : Type u} {source : Type v}
    [Group acting] [Group source] [MulDistribMulAction acting source]
    (normal : Subgroup source) [normal.Characteristic] :
    MulAction.QuotientAction acting normal := by
  constructor
  intro scalar first second hmem
  have hinvariant :=
    (Subgroup.characteristic_iff_le_comap.mp
      (inferInstance : normal.Characteristic)
      (MulDistribMulAction.toMulAut acting source scalar)) hmem
  change scalar • (first⁻¹ * second) ∈ normal at hinvariant
  simpa only [smul_mul', smul_inv'] using hinvariant

noncomputable abbrev characteristic_quotient_mulDistribMulAction
    {acting : Type u} {source : Type v}
    [Group acting] [Group source] [MulDistribMulAction acting source]
    (normal : Subgroup source) [normal.Normal] [normal.Characteristic] :
    MulDistribMulAction acting (source ⧸ normal) := by
  let : MulAction.QuotientAction acting normal :=
    characteristic_subgroup_quotientAction normal
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

theorem coprime_pGroup_action_trivial_of_frattini_trivial
    {acting : Type u} {source : Type v}
    [Group acting] [Group source] [Finite source]
    [MulDistribMulAction acting source]
    (prime : ℕ) [Fact prime.Prime] (hacting : IsPGroup prime acting)
    (hcoprime : ¬ prime ∣ Nat.card (frattini source))
    (htrivial : ∀ (scalar : acting) (element : source),
      (QuotientGroup.mk' (frattini source)) (scalar • element) =
        (QuotientGroup.mk' (frattini source)) element) :
    ∀ (scalar : acting) (element : source), scalar • element = element := by
  let : MulAction.QuotientAction acting (frattini source) :=
    characteristic_subgroup_quotientAction (frattini source)
  have hequivariant : ∀ (scalar : acting) (element : source),
      (QuotientGroup.mk' (frattini source)) (scalar • element) =
        scalar • (QuotientGroup.mk' (frattini source)) element := by
    intro scalar element
    exact (MulAction.Quotient.smul_mk (frattini source) scalar element).symm
  have hlift : ∀ element : source ⧸ frattini source,
      ∃ lift : source, (QuotientGroup.mk' (frattini source)) lift = element ∧
        ∀ scalar : acting, scalar • lift = lift := by
    intro element
    apply fixedPoint_lifts_of_prime_coprime_kernel prime hacting
      (QuotientGroup.mk' (frattini source))
      (QuotientGroup.mk'_surjective (frattini source)) hequivariant
    · simpa only [QuotientGroup.ker_mk'] using hcoprime
    · intro scalar
      obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (frattini source) element
      rw [← hequivariant]
      exact htrivial scalar lift
  have hgenerates : FixedPoints.subgroup acting source ⊔ frattini source = ⊤ := by
    apply top_unique
    intro element helement
    obtain ⟨lift, hequal, hfixed⟩ := hlift ((QuotientGroup.mk' (frattini source)) element)
    have hdifference : lift⁻¹ * element ∈ frattini source := by
      apply (QuotientGroup.eq_one_iff _).mp
      change (QuotientGroup.mk' (frattini source)) (lift⁻¹ * element) = 1
      rw [map_mul, map_inv, hequal, inv_mul_cancel]
    have hliftmem : lift ∈ FixedPoints.subgroup acting source := hfixed
    have hliftjoined : lift ∈ FixedPoints.subgroup acting source ⊔ frattini source :=
      (show FixedPoints.subgroup acting source ≤
        FixedPoints.subgroup acting source ⊔ frattini source from le_sup_left) hliftmem
    have hdifferencejoined : lift⁻¹ * element ∈
        FixedPoints.subgroup acting source ⊔ frattini source :=
      (show frattini source ≤ FixedPoints.subgroup acting source ⊔ frattini source from
        le_sup_right) hdifference
    have hproduct : lift * (lift⁻¹ * element) ∈
        FixedPoints.subgroup acting source ⊔ frattini source :=
      Subgroup.mul_mem _ hliftjoined hdifferencejoined
    simpa only [mul_inv_cancel_left] using hproduct
  have hfixedtop : FixedPoints.subgroup acting source = ⊤ :=
    frattini_nongenerating hgenerates
  intro scalar element
  have hfixed : element ∈ FixedPoints.subgroup acting source := by
    rw [hfixedtop]
    exact Subgroup.mem_top element
  exact hfixed scalar

theorem faithful_coprime_pGroup_action_on_frattini_quotient
    {acting : Type u} {source : Type v}
    [Group acting] [Group source] [Finite source]
    [MulDistribMulAction acting source]
    (prime : ℕ) [Fact prime.Prime] (hacting : IsPGroup prime acting)
    (hcoprime : ¬ prime ∣ Nat.card (frattini source))
    (hfaithful : Function.Injective (MulDistribMulAction.toMulAut acting source)) :
    letI := characteristic_quotient_mulDistribMulAction (acting := acting) (frattini source)
    Function.Injective (MulDistribMulAction.toMulAut acting (source ⧸ frattini source)) := by
  let := characteristic_quotient_mulDistribMulAction (acting := acting) (frattini source)
  let representation := MulDistribMulAction.toMulAut acting (source ⧸ frattini source)
  apply (MonoidHom.ker_eq_bot_iff representation).mp
  apply bot_unique
  intro scalar hscalar
  let : MulDistribMulAction representation.ker source :=
    MulDistribMulAction.compHom source representation.ker.subtype
  have htrivial : ∀ (kernelElement : representation.ker) (element : source),
      (QuotientGroup.mk' (frattini source)) (kernelElement • element) =
        (QuotientGroup.mk' (frattini source)) element := by
    intro kernelElement element
    change (QuotientGroup.mk' (frattini source)) ((kernelElement : acting) • element) =
      (QuotientGroup.mk' (frattini source)) element
    change representation kernelElement.val ((QuotientGroup.mk' (frattini source)) element) =
      (QuotientGroup.mk' (frattini source)) element
    rw [show representation kernelElement.val = 1 from kernelElement.property]
    rfl
  have hfixed := coprime_pGroup_action_trivial_of_frattini_trivial prime
    (hacting.to_subgroup representation.ker) hcoprime htrivial
  have haut : MulDistribMulAction.toMulAut acting source scalar = 1 := by
    ext element
    exact hfixed ⟨scalar, hscalar⟩ element
  apply Subgroup.mem_bot.mpr
  apply hfaithful
  simpa only [map_one] using haut

theorem odd_pSubgroup_twoCore_frattini_action_injective
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2)
    (hchar : IsCharTwoType ambient)
    {acting localGroup : Subgroup ambient}
    (hacting : IsPGroup prime acting) (hcontained : acting ≤ localGroup)
    (hlocal : IsTwoLocal localGroup) :
    letI := MulDistribMulAction.compHom
      (pCoreOf 2 localGroup)
      (((pCoreOf 2 localGroup).normalizerMonoidHom).comp
        (Subgroup.inclusion (hcontained.trans (subgroup_normalizes_pCoreOf 2 localGroup))))
    letI := characteristic_quotient_mulDistribMulAction
      (acting := acting) (frattini (pCoreOf 2 localGroup))
    Function.Injective (MulDistribMulAction.toMulAut acting
      (pCoreOf 2 localGroup ⧸ frattini (pCoreOf 2 localGroup))) := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let actionHom :=
    (((pCoreOf 2 localGroup).normalizerMonoidHom).comp
      (Subgroup.inclusion (hcontained.trans (subgroup_normalizes_pCoreOf 2 localGroup))))
  let := MulDistribMulAction.compHom
    (pCoreOf 2 localGroup) actionHom
  have hcoprime : ¬ prime ∣
      Nat.card (frattini (pCoreOf 2 localGroup)) := by
    obtain ⟨rank, hcard⟩ := IsPGroup.iff_card.mp
      ((pCoreOf_isPGroup 2 localGroup).to_subgroup
        (frattini (pCoreOf 2 localGroup)))
    apply hprime.coprime_iff_not_dvd.mp
    rw [hcard]
    simpa only [pow_one] using Nat.coprime_pow_primes 1 rank hprime (by norm_num) hodd
  have hfaithful : Function.Injective
      (MulDistribMulAction.toMulAut acting (pCoreOf 2 localGroup)) := by
    have hequal : MulDistribMulAction.toMulAut acting
        (pCoreOf 2 localGroup) = actionHom := by
      ext scalar element
      rfl
    rw [hequal]
    exact odd_pSubgroup_twoCore_action_injective prime hprime hodd hchar
      hacting hcontained hlocal
  exact faithful_coprime_pGroup_action_on_frattini_quotient prime hacting hcoprime hfaithful

end CFSG.PreuniquenessRankFour.Helpers
