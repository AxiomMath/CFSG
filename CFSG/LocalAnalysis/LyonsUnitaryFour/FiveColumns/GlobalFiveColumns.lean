module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.LocalFourier
public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.QuotientBlock
public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.Inflation
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.PrincipalSectionKernel

public section

open scoped BigOperators Classical

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed CFSG.RankTwoShapes

theorem sum_fiveFourier {X : Type*} [Monoid X] (f : X → ℂ) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5)
    (u v : X) : ∑ i ∈ Finset.range 5, fiveFourier f ζ u v i = f u := by
  simp only [fiveFourier, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ j ∈ Finset.range 5, ∑ i ∈ Finset.range 5, ζ ^ (4 * i * j) * f (u * v ^ j) =
      (if j = 0 then 5 else 0) * f (u * v ^ j) := by
    intro j hj
    rw [← Finset.sum_mul]
    congr 1
    rw [Finset.sum_congr rfl fun i _ => by rw [show 4 * i * j = (4 * j) * i by ring],
      sum_range_five_pow_mul hζ]
    have hiff : 5 ∣ 4 * j ↔ j = 0 := by
      have := Finset.mem_range.mp hj
      omega
    by_cases hj0 : j = 0
    · rw [ite_eq_left (hiff.mpr hj0), ite_eq_left hj0]
    · rw [ite_eq_right (fun h => hj0 (hiff.mp h)), ite_eq_right hj0]
  rw [Finset.sum_congr rfl hinner]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range]
  norm_num
  ring

theorem sum_fiveFourier_mul_conj {X ι : Type*} [Monoid X] (s : Finset ι) (F : ι → X → ℂ)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (u v : X) (i k : ℕ) :
    ∑ a ∈ s, fiveFourier (F a) ζ u v i * starRingEnd ℂ (fiveFourier (F a) ζ u v k) =
      (25 : ℂ)⁻¹ * ∑ j ∈ Finset.range 5, ∑ l ∈ Finset.range 5,
        ζ ^ (4 * i * j) * ζ ^ (16 * k * l) *
          ∑ a ∈ s, F a (u * v ^ j) * starRingEnd ℂ (F a (u * v ^ l)) := by
  have hexp : ∀ a, fiveFourier (F a) ζ u v i * starRingEnd ℂ (fiveFourier (F a) ζ u v k) =
      (25 : ℂ)⁻¹ * ∑ j ∈ Finset.range 5, ∑ l ∈ Finset.range 5,
        ζ ^ (4 * i * j) * ζ ^ (16 * k * l) *
          (F a (u * v ^ j) * starRingEnd ℂ (F a (u * v ^ l))) := by
    intro a
    simp only [fiveFourier, map_mul, map_sum, map_inv₀, conj_pow_of_pow_five hζ]
    have h5 : starRingEnd ℂ (5 : ℂ) = 5 := by
      rw [show (5 : ℂ) = ((5 : ℕ) : ℂ) by norm_num, Complex.conj_natCast]
    rw [h5, mul_mul_mul_comm, Finset.sum_mul_sum, show (5 : ℂ)⁻¹ * 5⁻¹ = 25⁻¹ by norm_num]
    congr 1
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [show 4 * (4 * k * l) = 16 * k * l by ring]
    ring
  rw [Finset.sum_congr rfl fun a _ => hexp a, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum]

theorem exists_odd_order_lift {C L : Type*} [Group C] [Finite C] [Group L] (π : C →* L)
    (hπ : Function.Surjective π) {h : L} (hh : h ^ 5 = 1) :
    ∃ y : C, π y = h ∧ Nat.Coprime 2 (orderOf y) := by
  obtain ⟨g, rfl⟩ := hπ h
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  refine ⟨g ^ (16 ^ a), ?_, ?_⟩
  · rw [map_pow]
    have h16 : 16 ^ a % 5 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    rw [← Nat.div_add_mod (16 ^ a) 5, h16, pow_add, pow_mul, hh, one_pow, one_mul, pow_one]
  · have hdvd : orderOf (g ^ (16 ^ a)) ∣ m := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul]
      have h16 : 16 ^ a * m = orderOf g * 8 ^ a := by
        rw [hn, show (16 : ℕ) = 2 * 8 by norm_num, mul_pow]
        ring
      rw [h16, pow_mul, pow_orderOf_eq_one, one_pow]
    exact Nat.Coprime.coprime_dvd_right hdvd (Nat.coprime_two_left.mpr hm)

variable {G : Type} [Group G] [Fintype G]

theorem global_fiveFourier_degree (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (blockLabel : basis.index) {u r : G}
    {e : ℕ} (hu : orderOf u ∣ 2 ^ e) (hu1 : u ≠ 1) (hr : Nat.Coprime 2 (orderOf r))
    (hur : Commute u r) (ζ : ℂ) (i : ℕ) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) blockLabel,
      (basis.representation χ).character 1 *
        fiveFourier (basis.representation χ).character ζ u r i = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simp only [fiveFourier, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hcol := coefficientBlock_section_column_orthogonality basis ideal 2 blockLabel u 1 (r ^ j) 1
    e 0 hu (by simp) (Nat.Coprime.coprime_dvd_right (orderOf_pow_dvd (x := r) j) hr) (by simp)
    (hur.pow_right j) (Commute.one_right 1) (fun hc => hu1 (isConj_one_right.mp hc.symm))
  simp only [mul_one, inv_one] at hcol
  calc ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) blockLabel,
        (basis.representation χ).character 1 * ((5 : ℂ)⁻¹ * (ζ ^ (4 * i * j) *
          (basis.representation χ).character (u * r ^ j)))
      = (5 : ℂ)⁻¹ * ζ ^ (4 * i * j) *
        ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) blockLabel,
          (basis.representation χ).character (u * r ^ j) *
            (basis.representation χ).character 1 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun χ _ => ?_
        ring
    _ = 0 := by rw [hcol, mul_zero]

theorem global_fiveFourier_mixed (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (blockLabel : basis.index) {u r t : G}
    {e e' : ℕ} (hu : orderOf u ∣ 2 ^ e) (ht : orderOf t ∣ 2 ^ e') (htu : ¬ IsConj u t)
    (hr : Nat.Coprime 2 (orderOf r)) (hur : Commute u r) (ζ : ℂ) (i : ℕ) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) blockLabel,
      starRingEnd ℂ ((basis.representation χ).character t) *
        fiveFourier (basis.representation χ).character ζ u r i = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simp only [fiveFourier, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hcol := coefficientBlock_section_column_orthogonality basis ideal 2 blockLabel u t (r ^ j) 1
    e e' hu ht (Nat.Coprime.coprime_dvd_right (orderOf_pow_dvd (x := r) j) hr) (by simp)
    (hur.pow_right j) (Commute.one_right t) htu
  simp only [mul_one] at hcol
  calc ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) blockLabel,
        starRingEnd ℂ ((basis.representation χ).character t) * ((5 : ℂ)⁻¹ *
          (ζ ^ (4 * i * j) * (basis.representation χ).character (u * r ^ j)))
      = (5 : ℂ)⁻¹ * ζ ^ (4 * i * j) *
        ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) blockLabel,
          (basis.representation χ).character (u * r ^ j) *
            (basis.representation χ).character t⁻¹ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [finite_character_conjugate_inverse]
        ring
    _ = 0 := by rw [hcol, mul_zero]

theorem local_principal_block_eq {z : G}
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers z : Set G)))
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    {L : Type} [Group L] [Fintype L] {S₀ : Subgroup L} {h : L} (hL : UnitaryFourByFive S₀ h)
    (quotientBasis : FiniteIrreducibleCharacterBasis L)
    (π : Subgroup.centralizer (Subgroup.zpowers z : Set G) →* L) (hπ : Function.Surjective π)
    [Fintype π.ker] (hker : ¬ 2 ∣ Nat.card π.ker) :
    coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal =
      normalSubgroupCharacterSupport localBasis π.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨label, -⟩ := finiteIrreducibleCharacterBasis_contains_irreducible quotientBasis
    (principalFiniteComplexRepresentation L) (principalFiniteComplexRepresentation_isIrreducible L)
  exact principal_block_eq_kernel_support_of_quotient localBasis quotientBasis ideal 2 π hπ hker
    label (hL.coefficientBlock_eq_univ quotientBasis ideal label) localPrincipal hlocalPrincipal

theorem global_fiveFourier_gram (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {z : G} (hz2 : z ^ 2 = 1)
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers z : Set G)))
    (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    {L : Type} [Group L] [Fintype L] {S₀ : Subgroup L} {h : L} (hL : UnitaryFourByFive S₀ h)
    (quotientBasis : FiniteIrreducibleCharacterBasis L)
    (π : Subgroup.centralizer (Subgroup.zpowers z : Set G) →* L) (hπ : Function.Surjective π)
    [Fintype π.ker] (hker : ¬ 2 ∣ Nat.card π.ker)
    (hz₀ : π (centralizerSelf z) ∈ (Subgroup.center S₀).map S₀.subtype)
    (y : Subgroup.centralizer (Subgroup.zpowers z : Set G)) (hy : π y = h)
    (hyodd : Nat.Coprime 2 (orderOf (y : G))) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) {i k : ℕ}
    (hi : i < 5) (hk : k < 5) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      fiveFourier (basis.representation χ).character ζ z (y : G) i *
        starRingEnd ℂ (fiveFourier (basis.representation χ).character ζ z (y : G) k) =
      if i = k then 16 else 12 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzord : orderOf z ∣ 2 ^ 1 := by rw [pow_one]; exact orderOf_dvd_of_pow_eq_one hz2
  rw [← hL.fiveFourier_gram quotientBasis hζ hz₀ hi hk, sum_fiveFourier_mul_conj _ _ hζ,
    sum_fiveFourier_mul_conj _ _ hζ]
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  congr 1
  have hblock := local_principal_block_eq localBasis ideal localPrincipal hlocalPrincipal hL
    quotientBasis π hπ hker
  have hreg : ∀ n : ℕ, ∃ r : Subgroup.centralizer (Subgroup.zpowers z : Set G),
      centralizerSelf z * y ^ n = centralizerSelf z * r ∧ Nat.Coprime 2 (orderOf r) := by
    intro n
    refine ⟨y ^ n, rfl, ?_⟩
    have hord : orderOf (y ^ n) ∣ orderOf (y : G) := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one (by
        rw [Subgroup.coe_pow, ← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow])
    exact Nat.Coprime.coprime_dvd_right hord hyodd
  have hkernel := brauer_principal_section_kernel basis ideal 2 principal hprincipal z 1 hzord
    localBasis localPrincipal hlocalPrincipal (centralizerSelf z * y ^ j)
    (centralizerSelf z * y ^ l) (hreg j) (hreg l)
  have hcoe : ∀ n : ℕ, ((centralizerSelf z * y ^ n : Subgroup.centralizer
      (Subgroup.zpowers z : Set G)) : G) = z * (y : G) ^ n := by
    intro n
    rw [Subgroup.coe_mul, Subgroup.coe_pow]
    rfl
  rw [hcoe j, hcoe l] at hkernel
  rw [hkernel, hblock]
  rw [sum_normalSubgroupCharacterSupport_eq localBasis quotientBasis π hπ
    (fun ψ => ψ (centralizerSelf z * y ^ j) * starRingEnd ℂ (ψ (centralizerSelf z * y ^ l)))]
  refine Finset.sum_congr rfl fun θ _ => ?_
  simp only [Function.comp_apply, map_mul, map_pow, hy]

theorem global_fiveFourier_integer (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {z : G} (hz2 : z ^ 2 = 1)
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers z : Set G)))
    (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    {L : Type} [Group L] [Fintype L] {S₀ : Subgroup L} {h : L} (hL : UnitaryFourByFive S₀ h)
    (quotientBasis : FiniteIrreducibleCharacterBasis L)
    (π : Subgroup.centralizer (Subgroup.zpowers z : Set G) →* L) (hπ : Function.Surjective π)
    [Fintype π.ker] (hker : ¬ 2 ∣ Nat.card π.ker)
    (hz₀ : π (centralizerSelf z) ∈ (Subgroup.center S₀).map S₀.subtype)
    (y : Subgroup.centralizer (Subgroup.zpowers z : Set G)) (hy : π y = h)
    (hyodd : Nat.Coprime 2 (orderOf (y : G))) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5)
    (χ : basis.index)
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (i : ℕ) : ∃ n : ℤ, fiveFourier (basis.representation χ).character ζ z (y : G) i = n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzord : orderOf z ∣ 2 ^ 1 := by rw [pow_one]; exact orderOf_dvd_of_pow_eq_one hz2
  set f : Subgroup.centralizer (Subgroup.zpowers z : Set G) → ℂ :=
    fun m => (basis.representation χ).character m.val with hf
  have hproj : ∀ j : ℕ, (basis.representation χ).character (z * (y : G) ^ j) =
      ∑ θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
        characterPairing f (localBasis.representation θ).character *
          (localBasis.representation θ).character (centralizerSelf z * y ^ j) := by
    intro j
    have hord : orderOf (((y ^ j)⁻¹ : Subgroup.centralizer (Subgroup.zpowers z : Set G)) : G) ∣
        orderOf (y : G) := by
      rw [Subgroup.coe_inv, orderOf_inv, Subgroup.coe_pow]
      exact orderOf_pow_dvd (x := (y : G)) j
    have hregular : Nat.Coprime 2
        (orderOf (((y ^ j)⁻¹ : Subgroup.centralizer (Subgroup.zpowers z : Set G)) : G)) :=
      Nat.Coprime.coprime_dvd_right hord hyodd
    have hloc := principal_local_section_projection_character basis ideal 2 principal hprincipal
      z 1 hzord localBasis localPrincipal hlocalPrincipal (y ^ j)⁻¹ hregular χ
    have hpoint : ((⟨z, element_mem_centralizer_zpowers z⟩ :
        Subgroup.centralizer (Subgroup.zpowers z : Set G)) * (y ^ j)⁻¹)⁻¹ =
        centralizerSelf z * y ^ j := by
      have hself : (centralizerSelf z)⁻¹ = centralizerSelf z := by
        apply Subtype.ext
        change z⁻¹ = z
        exact inv_eq_of_mul_eq_one_right (by rw [← pow_two, hz2])
      change (centralizerSelf z * (y ^ j)⁻¹)⁻¹ = _
      rw [mul_inv_rev, inv_inv, hself]
      exact ((centralizerSelf_commute z (y ^ j)).eq).symm
    rw [hpoint, characterSubsetProjection_character basis _ χ hχ,
      characterSubsetProjection_apply'] at hloc
    rw [show z * (y : G) ^ j = ((centralizerSelf z * y ^ j :
        Subgroup.centralizer (Subgroup.zpowers z : Set G)) : G) by
      rw [Subgroup.coe_mul, Subgroup.coe_pow]; rfl, ← hloc]
  have hfour : fiveFourier (basis.representation χ).character ζ z (y : G) i =
      ∑ θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
        characterPairing f (localBasis.representation θ).character *
          fiveFourier (localBasis.representation θ).character ζ (centralizerSelf z) y i := by
    simp only [fiveFourier, hproj, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun θ _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hfour, local_principal_block_eq localBasis ideal localPrincipal hlocalPrincipal hL
    quotientBasis π hπ hker, sum_normalSubgroupCharacterSupport_eq localBasis quotientBasis π hπ
    (fun ψ => characterPairing f ψ * fiveFourier ψ ζ (centralizerSelf z) y i)]
  have hz₀2 : π (centralizerSelf z) ^ 2 = 1 := by
    rw [← map_pow]
    have : centralizerSelf z ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]; exact hz2)
    rw [this, map_one]
  have hterm : ∀ θ : quotientBasis.index, ∃ n : ℤ,
      characterPairing f ((quotientBasis.representation θ).character ∘ π) *
        fiveFourier ((quotientBasis.representation θ).character ∘ π) ζ (centralizerSelf z) y i =
        n := by
    intro θ
    obtain ⟨m, hm⟩ := characterPairing_virtual_integer f
      ((quotientBasis.representation θ).character ∘ π)
      (character_mem_virtualCharacters
        (inflatedFiniteComplexRepresentation (Subgroup.centralizer
          (Subgroup.zpowers z : Set G)).subtype (basis.representation χ)))
      (character_mem_virtualCharacters
        (inflatedFiniteComplexRepresentation π (quotientBasis.representation θ)))
    obtain ⟨a, ha⟩ := hL.fiveFourier_integer quotientBasis hζ hz₀ hz₀2 θ i
    refine ⟨m * a, ?_⟩
    have hcomp : fiveFourier ((quotientBasis.representation θ).character ∘ π) ζ
        (centralizerSelf z) y i =
        fiveFourier (quotientBasis.representation θ).character ζ (π (centralizerSelf z)) h i := by
      simp only [fiveFourier, Function.comp_apply, map_mul, map_pow, hy]
    rw [hm, hcomp, ha]
    push_cast
    ring
  choose n hn using hterm
  exact ⟨∑ θ, n θ, by rw [Int.cast_sum]; exact Finset.sum_congr rfl fun θ _ => hn θ⟩

end CFSG.LyonsUnitaryFour
