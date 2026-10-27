module

public import CFSG.CharacterTheory.TwoRankLowerBound.PrincipalSectionIntertwining
public import CFSG.CharacterTheory.TwoRankLowerBound.BlockSectionMask
public import CFSG.CharacterTheory.Wreathed.WeightedCentralInvolutionSum

public section

namespace CFSG.RankTwoShapes

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed
open scoped BigOperators Classical

theorem primary_regular_coprime_iff {G : Type*} [Group G] {p : ℕ}
    (x y : G) (e : ℕ) (hx : orderOf x ∣ p ^ e) (hy : Nat.Coprime p (orderOf y))
    (hxy : Commute x y) : Nat.Coprime p (orderOf (x * y)) ↔ x = 1 := by
  have hcop : Nat.Coprime (orderOf x) (orderOf y) := (hy.pow_left e).of_dvd_left hx
  rw [hxy.orderOf_mul_eq_mul_orderOf_of_coprime hcop, Nat.coprime_mul_iff_right]
  constructor
  · rintro ⟨h1, -⟩
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (h1.pow_left e).symm hx)
  · rintro rfl
    simpa using hy

@[expose] def centralizerSelf {G : Type*} [Group G] (u : G) :
    Subgroup.centralizer (Subgroup.zpowers u : Set G) :=
  ⟨u, element_mem_centralizer_zpowers u⟩

theorem centralizerSelf_commute {G : Type*} [Group G] (u : G)
    (h : Subgroup.centralizer (Subgroup.zpowers u : Set G)) :
    Commute (centralizerSelf u) h := by
  apply Subtype.ext
  change u * h.val = h.val * u
  exact Subgroup.mem_centralizer_iff.mp h.property u (Subgroup.mem_zpowers u)

theorem centralizerSelf_mem_center {G : Type*} [Group G] (u : G) :
    centralizerSelf u ∈ Subgroup.center (Subgroup.centralizer (Subgroup.zpowers u : Set G)) :=
  Subgroup.mem_center_iff.mpr fun h => (centralizerSelf_commute u h).eq.symm

@[expose] def inverseSection {G : Type*} [Group G] (p : ℕ) (u : G) :
    Set (Subgroup.centralizer (Subgroup.zpowers u : Set G)) :=
  {h | Nat.Coprime p (orderOf (centralizerSelf u * h))}

theorem inverseSection_primary_iff {G : Type*} [Group G] (p : ℕ) (u : G) (E : ℕ)
    (hu : orderOf u ∣ p ^ E) (x y : Subgroup.centralizer (Subgroup.zpowers u : Set G)) (k : ℕ)
    (hx : orderOf x ∣ p ^ k) (hy : Nat.Coprime p (orderOf y)) (hxy : Commute x y) :
    x * y ∈ inverseSection p u ↔ centralizerSelf u * x = 1 := by
  change Nat.Coprime p (orderOf (centralizerSelf u * (x * y))) ↔ _
  rw [← mul_assoc]
  apply primary_regular_coprime_iff _ y (E + k) _ hy
  · exact (centralizerSelf_commute u y).mul_left hxy
  · have hcx := centralizerSelf_commute u x
    refine hcx.orderOf_mul_dvd_mul_orderOf.trans ?_
    rw [pow_add]
    apply Nat.mul_dvd_mul _ hx
    rw [centralizerSelf, Subgroup.orderOf_mk]
    exact hu

theorem inverseSection_primeSectionUnion {G : Type*} [Group G] (p : ℕ) (u : G) (E : ℕ)
    (hu : orderOf u ∣ p ^ E) : primeSectionUnion p (inverseSection p u) := by
  intro a a' b b' e e' ha ha' hb hb' hab ha'b' hconj
  rw [inverseSection_primary_iff p u E hu a b e ha hb hab,
    inverseSection_primary_iff p u E hu a' b' e' ha' hb' ha'b']
  rw [mul_eq_one_iff_eq_inv', mul_eq_one_iff_eq_inv']
  have hcenter : (centralizerSelf u)⁻¹ ∈
      Set.center (Subgroup.centralizer (Subgroup.zpowers u : Set G)) := by
    rw [← Subgroup.coe_center]
    exact Subgroup.inv_mem _ (centralizerSelf_mem_center u)
  constructor
  · intro heq
    subst heq
    exact (hconj.eq_of_left_mem_center hcenter).symm
  · intro heq
    subst heq
    exact hconj.symm.eq_of_left_mem_center hcenter |>.symm

theorem inv_centralizerSelf_mem_inverseSection {G : Type*} [Group G] (p : ℕ) (u : G) :
    (centralizerSelf u)⁻¹ ∈ inverseSection p u := by
  change Nat.Coprime p (orderOf (centralizerSelf u * (centralizerSelf u)⁻¹))
  rw [mul_inv_cancel, orderOf_one]
  exact Nat.coprime_one_right p

theorem centralizer_singleton_inv_eq {G : Type*} [Group G] (u : G) :
    Subgroup.centralizer {u⁻¹} = Subgroup.centralizer (Subgroup.zpowers u : Set G) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hc : Commute g u⁻¹ := h
    have hc' : Commute g u := by simpa using hc.inv_right
    exact (hc'.zpow_right k).eq.symm
  · intro h
    have hc : Commute g u := (h u (Subgroup.mem_zpowers u)).symm
    exact hc.inv_right.eq

theorem mask_conjugatorCount_eq {G : Type*} [Group G] [Fintype G] (p : ℕ) (u : G) (E : ℕ)
    (hu : orderOf u ∣ p ^ E) :
    characterFunctionMask (inverseSection p u)
        (fun h : Subgroup.centralizer (Subgroup.zpowers u : Set G) => conjugatorCount u⁻¹ h.val) =
      fun h => if h = (centralizerSelf u)⁻¹ then conjugatorCount u⁻¹ u⁻¹ else 0 := by
  funext h
  unfold characterFunctionMask
  by_cases hD : h ∈ inverseSection p u
  · rw [ite_eq_left hD]
    by_cases hh : h = (centralizerSelf u)⁻¹
    · rw [ite_eq_left hh, hh]
      rfl
    · rw [ite_eq_right hh]
      unfold conjugatorCount
      apply Finset.sum_eq_zero
      intro x _
      rw [ite_eq_right]
      intro hx
      apply hh
      have horder : orderOf h ∣ p ^ E := by
        rw [← Subgroup.orderOf_coe, ← hx]
        have := (MulAut.conj x).orderOf_eq u⁻¹
        change orderOf (x * u⁻¹ * x⁻¹) = orderOf u⁻¹ at this
        rw [this, orderOf_inv]
        exact hu
      have hone := (inverseSection_primary_iff p u E hu h 1 E horder
        (by rw [orderOf_one]; exact Nat.coprime_one_right p) (Commute.one_right h)).mp
        (by simpa using hD)
      exact eq_inv_of_mul_eq_one_right hone
  · rw [ite_eq_right hD, ite_eq_right]
    rintro rfl
    exact hD (inv_centralizerSelf_mem_inverseSection p u)

theorem characterSubsetProjection_apply' {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (support : Finset basis.index) (function : G → ℂ)
    (element : G) :
    characterSubsetProjection basis support function element =
      ∑ label ∈ support, characterPairing function (basis.representation label).character *
        (basis.representation label).character element := by
  simp only [characterSubsetProjection, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]

theorem irreducible_character_central_mul_inv {G : Type*} [Group G] [Fintype G]
    (data : FiniteComplexRepresentation G) (hirreducible : data.IsIrreducible)
    (c : G) (hc : c ∈ Subgroup.center G) :
    data.character c * data.character c⁻¹ = data.character 1 ^ 2 := by
  let : data.representation.IsIrreducible := hirreducible
  have hdegree := irreducible_character_degree_ne_zero data hirreducible
  have hinvariant : ∀ (x : G) (conjugator element : G),
      x ∈ Subgroup.center G →
        (element ∈ ({x} : Finset G) ↔ conjugator * element * conjugator⁻¹ ∈ ({x} : Finset G)) := by
    intro x conjugator element hx
    simp only [Finset.mem_singleton]
    constructor
    · rintro rfl
      rw [Subgroup.mem_center_iff.mp hx conjugator, mul_inv_cancel_right]
    · intro h
      have h' : conjugator * element * conjugator⁻¹ = conjugator * x * conjugator⁻¹ := by
        rw [h, Subgroup.mem_center_iff.mp hx conjugator, mul_inv_cancel_right]
      simpa using h'
  have hscalar := fun (x : G) (hx : x ∈ Subgroup.center G) =>
    irreducible_conjugacy_class_sum data.representation x {x}
      (fun conjugator element => hinvariant x conjugator element hx)
      (fun element helement => by
        rw [Finset.mem_singleton] at helement
        rw [helement])
      hdegree
  have hc' : c⁻¹ ∈ Subgroup.center G := Subgroup.inv_mem _ hc
  have h1 := hscalar c hc
  have h2 := hscalar c⁻¹ hc'
  simp only [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, one_mul] at h1 h2
  have hprod : data.representation c * data.representation c⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  rw [h1, h2, smul_mul_smul, one_mul] at hprod
  have htrace := congrArg (LinearMap.trace ℂ data.vector) hprod
  rw [map_smul, LinearMap.trace_one] at htrace
  have hdim : (Module.finrank ℂ data.vector : ℂ) = data.character 1 := by
    rw [FiniteComplexRepresentation.character, Representation.char_one]
  rw [hdim, smul_eq_mul] at htrace
  have hratio :
      data.character c / data.character 1 * (data.character c⁻¹ / data.character 1) = 1 := by
    have := mul_right_cancel₀ hdegree (htrace.trans (one_mul _).symm)
    exact this
  field_simp at hratio
  linear_combination hratio

theorem principal_primary_column_centralizer_norm {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (prime : ℕ) [Fact prime.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (u : G) (exponent : ℕ) (hu : orderOf u ∣ prime ^ exponent)
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers u : Set G)))
    (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1) :
    ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation label).character u *
          starRingEnd ℂ ((basis.representation label).character u) =
      ∑ label ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
        (localBasis.representation label).character 1 ^ 2 := by
  have hreg : Nat.Coprime prime
      (orderOf ((1 : Subgroup.centralizer (Subgroup.zpowers u : Set G)) : G)) := by simp
  have hlocal := principal_local_section_projection basis ideal prime principal hprincipal u
    exponent hu localBasis localPrincipal hlocalPrincipal 1 hreg (conjugatorCount u⁻¹)
    (conjugatorCount_conjugation u⁻¹)
  have hpoint : ((⟨u, element_mem_centralizer_zpowers u⟩ :
      Subgroup.centralizer (Subgroup.zpowers u : Set G)) * 1)⁻¹ = (centralizerSelf u)⁻¹ := by
    rw [mul_one]
    rfl
  rw [hpoint] at hlocal
  have hambient : characterSubsetProjection basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
      (conjugatorCount u⁻¹) ((centralizerSelf u)⁻¹ :
        Subgroup.centralizer (Subgroup.zpowers u : Set G)).val =
      ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation label).character u *
          starRingEnd ℂ ((basis.representation label).character u) := by
    rw [characterSubsetProjection_apply']
    apply Finset.sum_congr rfl
    intro label _
    rw [conjugatorCount_pairing, inv_inv, finite_character_conjugate_inverse]
    rfl
  have hmask := congrFun (coefficientBlock_section_mask_commute localBasis ideal prime
    localPrincipal (inverseSection prime u) (inverseSection_primeSectionUnion prime u exponent hu)
    (fun h : Subgroup.centralizer (Subgroup.zpowers u : Set G) => conjugatorCount u⁻¹ h.val))
    (centralizerSelf u)⁻¹
  have hmem := inv_centralizerSelf_mem_inverseSection prime u
  have hunmask : characterFunctionMask (inverseSection prime u)
      (characterSubsetProjection localBasis
        (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal)
        fun h : Subgroup.centralizer (Subgroup.zpowers u : Set G) => conjugatorCount u⁻¹ h.val)
        (centralizerSelf u)⁻¹ =
      characterSubsetProjection localBasis
        (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal)
        (fun h : Subgroup.centralizer (Subgroup.zpowers u : Set G) => conjugatorCount u⁻¹ h.val)
        (centralizerSelf u)⁻¹ := by
    unfold characterFunctionMask
    rw [ite_eq_left hmem]
  rw [hunmask, mask_conjugatorCount_eq prime u exponent hu] at hmask
  have hcard : (conjugatorCount u⁻¹ u⁻¹ : ℂ) =
      (Nat.card (Subgroup.centralizer (Subgroup.zpowers u : Set G)) : ℂ) := by
    rw [conjugatorCount_self, centralizer_singleton_inv_eq]
  have hlocalValue : characterSubsetProjection localBasis
      (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal)
      (fun h : Subgroup.centralizer (Subgroup.zpowers u : Set G) =>
        if h = (centralizerSelf u)⁻¹ then conjugatorCount u⁻¹ u⁻¹ else 0) (centralizerSelf u)⁻¹ =
      ∑ label ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
        (localBasis.representation label).character 1 ^ 2 := by
    rw [characterSubsetProjection_apply']
    apply Finset.sum_congr rfl
    intro label _
    have hpair : characterPairing (fun h : Subgroup.centralizer (Subgroup.zpowers u : Set G) =>
          if h = (centralizerSelf u)⁻¹ then conjugatorCount u⁻¹ u⁻¹ else 0)
        (localBasis.representation label).character =
        (Nat.card (Subgroup.centralizer (Subgroup.zpowers u : Set G)) : ℂ)⁻¹ *
          (conjugatorCount u⁻¹ u⁻¹ *
            (localBasis.representation label).character (centralizerSelf u)) := by
      unfold characterPairing
      congr 1
      rw [Finset.sum_eq_single (centralizerSelf u)⁻¹]
      · dsimp only
        rw [ite_eq_left rfl, inv_inv]
      · intro h _ hne
        dsimp only
        rw [ite_eq_right hne, zero_mul]
      · intro hnot
        exact absurd (Finset.mem_univ _) hnot
    rw [hpair, hcard]
    have hcentral := irreducible_character_central_mul_inv (localBasis.representation label)
      (localBasis.irreducible label) (centralizerSelf u) (centralizerSelf_mem_center u)
    have hne : (Nat.card (Subgroup.centralizer (Subgroup.zpowers u : Set G)) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    rw [← hcentral]
    field_simp
  rw [hlocalValue] at hmask
  rw [← hambient, ← hlocal, ← hmask]

theorem principal_block_degree_square_sum_of_normal_complement {H : Type*} [Group H] [Fintype H]
    (basis : FiniteIrreducibleCharacterBasis H) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (prime : ℕ) [Fact prime.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (N : Subgroup H) [N.Normal] (hcoprime : Nat.Coprime prime (Nat.card N))
    (hquotient : IsPGroup prime (H ⧸ N)) :
    ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation label).character 1 ^ 2 = (Nat.card (H ⧸ N) : ℂ) := by
  let R := localizedComplexIntegerRing ideal
  let := localizedComplexIntegerRing_residue_charP ideal prime
  set K := (QuotientGroup.mk' N).ker with hK
  have hKN : K = N := QuotientGroup.ker_mk' N
  have hunit : IsUnit ((Nat.card K : ℤ) : R) := by
    rw [localizedComplexInteger_integer_unit_iff ideal prime]
    rw [hKN]
    intro hdvd
    have hdvd' : prime ∣ Nat.card N := Int.natCast_dvd_natCast.mp hdvd
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : prime.Prime)).mp hcoprime hdvd'
  let cardUnit : Rˣ := hunit.unit
  have hcardUnit : (cardUnit : R) = Nat.card K := by
    change ((hunit.unit : Rˣ) : R) = _
    rw [IsUnit.unit_spec, Int.cast_natCast]
  have hblock := normalComplement_characterSupport_eq_block basis R prime (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) hquotient cardUnit hcardUnit principal
    (normalSubgroupCharacterSupport_principal_mem basis K principal hprincipal)
  rw [hblock]
  let complexUnit : ℂˣ := Units.mk0 (Nat.card K) (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hidem := normalSubgroupAverage_eq_characterSubsetIdempotent basis K complexUnit rfl
  have hcoeff := congrArg (fun value : MonoidAlgebra ℂ H => value.coeff 1) hidem
  rw [characterSubsetIdempotent_coeff] at hcoeff
  have hleft : (normalSubgroupAverage K complexUnit).coeff 1 = ((Nat.card K : ℂ))⁻¹ := by
    simp only [normalSubgroupAverage, Units.smul_def, MonoidAlgebra.coeff_smul,
      MonoidAlgebra.coeff_sum, Finsupp.smul_apply, Finsupp.finsetSum_apply,
      MonoidAlgebra.coeff_single, Finsupp.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (1 : K)]
    · simp [complexUnit]
    · intro k _ hk
      have hk' : (k : H) ≠ 1 := fun h => hk (Subtype.ext h)
      rw [ite_eq_right hk']
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hleft] at hcoeff
  have hsum : ∑ label ∈ normalSubgroupCharacterSupport basis K,
      (basis.representation label).character 1 / (Nat.card H : ℂ) *
        (basis.representation label).character 1⁻¹ =
      (∑ label ∈ normalSubgroupCharacterSupport basis K,
        (basis.representation label).character 1 ^ 2) / (Nat.card H : ℂ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro label _
    rw [inv_one]
    ring
  rw [hsum] at hcoeff
  have hH : (Nat.card H : ℂ) = (Nat.card (H ⧸ N) : ℂ) * (Nat.card K : ℂ) := by
    rw [hKN]
    exact_mod_cast Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hKne : (Nat.card K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hHne : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [eq_div_iff hHne] at hcoeff
  rw [← hcoeff, hH]
  field_simp

theorem card_quotient_eq_card_sylow_of_normal_complement {H : Type*} [Group H] [Finite H]
    (prime : ℕ) [Fact prime.Prime] (N : Subgroup H) [N.Normal]
    (hcoprime : Nat.Coprime prime (Nat.card N)) (hquotient : IsPGroup prime (H ⧸ N))
    (P : Sylow prime H) : Nat.card (H ⧸ N) = Nat.card P := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hquotient
  rw [Sylow.card_eq_multiplicity, Subgroup.card_eq_card_quotient_mul_card_subgroup N, hk]
  have hprime : prime.Prime := Fact.out
  have hNpos : Nat.card N ≠ 0 := Nat.card_pos.ne'
  rw [Nat.factorization_mul (pow_ne_zero _ hprime.ne_zero) hNpos, Finsupp.add_apply,
    hprime.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hprime).mp hcoprime),
    add_zero]

theorem principal_primary_column_centralizer_norm_of_normal_complement {G : Type*} [Group G]
    [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (prime : ℕ) [Fact prime.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (u : G) (exponent : ℕ) (hu : orderOf u ∣ prime ^ exponent)
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers u : Set G)))
    (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (N : Subgroup (Subgroup.centralizer (Subgroup.zpowers u : Set G))) [N.Normal]
    (hcoprime : Nat.Coprime prime (Nat.card N))
    (hquotient : IsPGroup prime (Subgroup.centralizer (Subgroup.zpowers u : Set G) ⧸ N)) :
    (∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation label).character u *
          starRingEnd ℂ ((basis.representation label).character u) =
      ∑ label ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
        (localBasis.representation label).character 1 ^ 2) ∧
    (∑ label ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
        (localBasis.representation label).character 1 ^ 2 =
      (Nat.card (Subgroup.centralizer (Subgroup.zpowers u : Set G) ⧸ N) : ℂ)) ∧
    ∀ P : Sylow prime (Subgroup.centralizer (Subgroup.zpowers u : Set G)),
      Nat.card (Subgroup.centralizer (Subgroup.zpowers u : Set G) ⧸ N) = Nat.card P :=
  ⟨principal_primary_column_centralizer_norm basis ideal prime principal hprincipal u exponent hu
      localBasis localPrincipal hlocalPrincipal,
    principal_block_degree_square_sum_of_normal_complement localBasis ideal prime localPrincipal
      hlocalPrincipal N hcoprime hquotient,
    card_quotient_eq_card_sylow_of_normal_complement prime N hcoprime hquotient⟩

end CFSG.RankTwoShapes
