module

public import CFSG.CharacterTheory.Wreathed.ConditionalSquareRootColumns
public import CFSG.CharacterTheory.Wreathed.ConditionalSquareRootParity

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.ConditionalSquareRoot

open CFSG.Wreathed CFSG.Wreathed.WreathCentralSquare CFSG.Wreathed.SquareRootSmallCharacterRigidity
  CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal CFSG.Wreathed.ConditionalFourier

variable {G : Type} [Group G] [Fintype G]

theorem actualRoot_odd_power_rows_orthogonal (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (C : ℕ → Subgroup G)
    (hC : ∀ k, C k = Subgroup.centralizer {wreathModelHom S e (Original.a (2 ^ n)) ^ k})
    (Φ : G → ℂ) (hΦreal : ∀ g, conj (Φ g) = Φ g) (ε : ℤ) (q : ℕ)
    (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hdata : ∀ k ∈ Finset.Ico 1 (2 ^ n), ∀ (localBasis : FiniteIrreducibleCharacterBasis (C k))
      (localPrincipal : localBasis.index),
      (localBasis.representation localPrincipal).character = 1 →
        PrincipalRegularIntegralBasisData localBasis ideal localPrincipal (fun c => Φ c) ε q M)
    (v : basis.index → ℕ → Fin 2 → ℂ)
    (hv : IsCentralSectionRows basis ideal principal (wreathModelHom S e (Original.a (2 ^ n)))
      (2 ^ n) C Φ ε v)
    {h : ℤ} (hh : Odd h) {k : ℕ} (hk : k ∈ Finset.Ico 1 (2 ^ n)) (ℓ : Fin 2) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character (actualRoot S e ^ h) * conj (v χ k ℓ) = 0 := by
  set B₀ := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB₀
  set a := wreathModelHom S e (Original.a (2 ^ n)) with ha_def
  obtain ⟨lb⟩ := finiteIrreducibleCharacterBasis_exists (G := C k)
  obtain ⟨l0, hl0⟩ := finiteIrreducibleCharacterBasis_contains_irreducible lb
    (principalFiniteComplexRepresentation _) (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hl0
  have hreg := hdata k hk lb l0 hl0
  set α := ∑ χ ∈ B₀, (basis.representation χ).character (actualRoot S e ^ h) * conj (v χ k 0)
    with hα
  set β := ∑ χ ∈ B₀, (basis.representation χ).character (actualRoot S e ^ h) * conj (v χ k 1)
    with hβ
  have hcomb : ∀ r : C k, Odd (orderOf r) → α + β * (1 + ε * Φ r) = 0 := by
    intro r hr
    have hrodd : Odd (orderOf (r : G)) := by rwa [Subgroup.orderOf_coe]
    have hrmem : (r : G) ∈ Subgroup.centralizer {a ^ k} := hC k ▸ r.2
    have horth := actualRoot_odd_power_column_orthogonal_central n hn S e basis ideal principal
      hprincipal hh k r hrmem hrodd
    rw [← ha_def] at horth
    rw [← horth, hα, hβ, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [hv χ hχ k hk r r.2 hrodd]
    simp only [map_add, map_mul, map_one, map_intCast, hΦreal]
    ring
  have hzero := eq_zero_of_odd_combination (fun c : C k => Φ c) ε q hreg.degree
    hreg.linearIndependent hcomb
  obtain rfl | rfl : ℓ = 0 ∨ ℓ = 1 := by fin_cases ℓ <;> simp
  · exact hzero.1
  · exact hzero.2

theorem signed_even_fourier_orthogonal (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (C : ℕ → Subgroup G)
    (hC : ∀ k, C k = Subgroup.centralizer {wreathModelHom S e (Original.a (2 ^ n)) ^ k})
    (Φ : G → ℂ) (hΦreal : ∀ g, conj (Φ g) = Φ g) (ε : ℤ) (q : ℕ)
    (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hdata : ∀ k ∈ Finset.Ico 1 (2 ^ n), ∀ (localBasis : FiniteIrreducibleCharacterBasis (C k))
      (localPrincipal : localBasis.index),
      (localBasis.representation localPrincipal).character = 1 →
        PrincipalRegularIntegralBasisData localBasis ideal localPrincipal (fun c => Φ c) ε q M)
    (v : basis.index → ℕ → Fin 2 → ℂ)
    (hv : IsCentralSectionRows basis ideal principal (wreathModelHom S e (Original.a (2 ^ n)))
      (2 ^ n) C Φ ε v)
    {η : ℂ} (hη : IsPrimitiveRoot η (2 * 2 ^ n)) (ζ : ℂ)
    (F : basis.index → ℤ) {j : ℕ} (ℓ : Fin 2)
    (hF : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (F χ : ℂ) = fourierTransform (2 ^ n) ζ (fun k => v χ k ℓ) j) (r : ℕ) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      signedEvenEigenmultiplicity (basis.representation χ) (actualRoot S e) η (2 ^ n) r * F χ =
        0 := by
  set B₀ := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB₀
  set y := actualRoot S e with hy
  set M₀ := 2 ^ n / 2 with hM₀
  apply Int.cast_injective (α := ℂ)
  push_cast
  have hrow : ∀ i ∈ Finset.range M₀, ∀ k ∈ Finset.Ico 1 (2 ^ n),
      ∑ χ ∈ B₀, (basis.representation χ).character (y ^ (2 * i + 1)) * conj (v χ k ℓ) = 0 := by
    intro i _ k hk
    have hodd : Odd ((2 * i + 1 : ℕ) : ℤ) := ⟨i, by push_cast; ring⟩
    have h := actualRoot_odd_power_rows_orthogonal n hn S e basis ideal principal hprincipal C hC
      Φ hΦreal ε q M hdata v hv hodd hk ℓ
    rwa [zpow_natCast] at h
  calc ∑ χ ∈ B₀, (signedEvenEigenmultiplicity (basis.representation χ) y η (2 ^ n) r : ℂ) *
        (F χ : ℂ)
      = ∑ χ ∈ B₀, ((M₀ : ℂ)⁻¹ * ∑ i ∈ Finset.range M₀,
          (η ^ 2)⁻¹ ^ (r * (2 * i + 1)) * (basis.representation χ).character (y ^ (2 * i + 1))) *
          conj (((2 ^ n : ℕ) : ℂ)⁻¹ *
            ∑ k ∈ Finset.Ico 1 (2 ^ n), (ζ ^ (j * k) - 1) * v χ k ℓ) := by
        refine Finset.sum_congr rfl fun χ hχ => ?_
        rw [actualRoot_signed_even_inversion n hn S e (basis.representation χ) hη r]
        congr 1
        rw [← map_intCast (starRingEnd ℂ) (F χ), hF χ hχ]
        rfl
    _ = ∑ χ ∈ B₀, ∑ i ∈ Finset.range M₀, ∑ k ∈ Finset.Ico 1 (2 ^ n),
          ((M₀ : ℂ)⁻¹ * ((2 ^ n : ℕ) : ℂ)⁻¹) * ((η ^ 2)⁻¹ ^ (r * (2 * i + 1)) *
            conj (ζ ^ (j * k) - 1) * ((basis.representation χ).character (y ^ (2 * i + 1)) *
              conj (v χ k ℓ))) := by
        refine Finset.sum_congr rfl fun χ _ => ?_
        simp only [map_mul, map_sum, map_inv₀, map_natCast]
        rw [mul_mul_mul_comm, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = ((M₀ : ℂ)⁻¹ * ((2 ^ n : ℕ) : ℂ)⁻¹) * ∑ i ∈ Finset.range M₀,
          ∑ k ∈ Finset.Ico 1 (2 ^ n), (η ^ 2)⁻¹ ^ (r * (2 * i + 1)) * conj (ζ ^ (j * k) - 1) *
            ∑ χ ∈ B₀, (basis.representation χ).character (y ^ (2 * i + 1)) *
              conj (v χ k ℓ) := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
    _ = 0 := by
        rw [Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun k hk => by
          rw [hrow i hi k hk, mul_zero], mul_zero]

theorem fourier_rows_at_one_eigen (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (principal : basis.index) (C : ℕ → Subgroup G) (Φ : G → ℂ) (ε : ℤ)
    (q : ℕ) (hq : Φ 1 = q) (v : basis.index → ℕ → Fin 2 → ℂ)
    (hv : IsCentralSectionRows basis ideal principal (wreathModelHom S e (Original.a (2 ^ n)))
      (2 ^ n) C Φ ε v)
    {η : ℂ} (hη : IsPrimitiveRoot η (2 * 2 ^ n)) {ζ : ℂ} (hηζ : η ^ 2 = ζ)
    {χ : basis.index}
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    {j : ℕ} (hj : j ∈ Finset.Ico 1 (2 ^ n)) :
    fourierTransform (2 ^ n) ζ (fun k => v χ k 0) j +
        (1 + ε * q) * fourierTransform (2 ^ n) ζ (fun k => v χ k 1) j =
      (((cyclicEigenmultiplicity (basis.representation χ) (actualRoot S e) η (2 ^ n - j) : ℤ) +
        cyclicEigenmultiplicity (basis.representation χ) (actualRoot S e) η (2 * 2 ^ n - j) -
        cyclicEigenmultiplicity (basis.representation χ) (actualRoot S e) η 0 -
        cyclicEigenmultiplicity (basis.representation χ) (actualRoot S e) η (2 ^ n) : ℤ) : ℂ) := by
  rw [Finset.mem_Ico] at hj
  set y := actualRoot S e with hy
  have hm : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hy2m : y ^ (2 * 2 ^ n) = 1 := by
    rw [← actualRoot_orderOf n hn S e]
    exact pow_orderOf_eq_one _
  rw [← fourier_character_square_powers (basis.representation χ) y hm hy2m hη hj.1 hj.2, hηζ]
  have hval : ∀ k ∈ Finset.Ico 1 (2 ^ n), v χ k 0 + (1 + ε * q) * v χ k 1 =
      (basis.representation χ).character (y ^ (2 * k)) := by
    intro k hk
    have h := hv χ hχ k hk 1 (Subgroup.one_mem _) (by rw [orderOf_one]; exact odd_one)
    rw [mul_one, hq] at h
    rw [pow_mul, actualRoot_sq, h]
    ring
  unfold fourierTransform
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) hm,
    Finset.sum_Ico_succ_top (Nat.zero_le 0), Finset.Ico_self, Finset.sum_empty]
  simp only [mul_zero, pow_zero, sub_self, zero_mul, zero_add]
  have hsum : ∑ k ∈ Finset.Ico 1 (2 ^ n), (ζ ^ (j * k) - 1) *
      (basis.representation χ).character (y ^ (2 * k)) =
      ∑ k ∈ Finset.Ico 1 (2 ^ n), (ζ ^ (j * k) - 1) * (v χ k 0 + (1 + ε * q) * v χ k 1) :=
    Finset.sum_congr rfl fun k hk => by rw [hval k hk]
  rw [hsum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end CFSG.Wreathed.ConditionalSquareRoot
