module

public import CFSG.CharacterTheory.Wreathed.ConditionalFlatCentralFourierRows
public import CFSG.CharacterTheory.Wreathed.ConditionalSquareRootColumns
public import CFSG.CharacterTheory.Wreathed.ConditionalSquareRootParity

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.FlatSquareRoot

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.ConditionalFourier
  CFSG.Wreathed.ConditionalSquareRoot CFSG.Wreathed.WreathCentralSquare
  CFSG.Wreathed.SquareRootSmallCharacterRigidity CFSG.Wreathed.FlatCentralFourier

variable {G : Type} [Group G] [Fintype G]

theorem flat_root_rows_orthogonal (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (B : basis.index)
    (C : ℕ → Subgroup G)
    (hC : ∀ k, C k = Subgroup.centralizer {wreathModelHom S e (Original.a (2 ^ n)) ^ k})
    (lamG ΦG : G → ℂ) (hΦreal : ∀ g, conj (ΦG g) = ΦG g) (ε : ℤ)
    (hlam0 : ∀ k ∈ Finset.Ico 1 (2 ^ n), ∀ c ∈ C k, lamG c ≠ 0)
    (hindep : ∀ k ∈ Finset.Ico 1 (2 ^ n), ∀ α β : ℂ,
      (∀ y ∈ C k, Odd (orderOf y) → α + β * (1 + ε * ΦG y) = 0) → α = 0 ∧ β = 0)
    (v : basis.index → ℕ → Fin 2 → ℂ)
    (hv : IsTwistedCentralSectionRows basis ideal B (wreathModelHom S e (Original.a (2 ^ n)))
      (2 ^ n) C lamG ΦG ε v)
    {h : ℤ} (hh : Odd h)
    (hvan : ∀ g : G, (∀ a c : G, a * c = g → Commute a c → (∃ e : ℕ, orderOf a = 2 ^ e) →
        Odd (orderOf c) → ¬ IsConj a (actualRoot S e ^ h)) →
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        (basis.representation χ).character (actualRoot S e ^ h) *
          conj ((basis.representation χ).character g) = 0)
    {k : ℕ} (hk : k ∈ Finset.Ico 1 (2 ^ n)) (ℓ : Fin 2) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
      (basis.representation χ).character (actualRoot S e ^ h) * conj (v χ k ℓ) = 0 := by
  set a := wreathModelHom S e (Original.a (2 ^ n)) with ha_def
  have hy2 : orderOf (actualRoot S e) = 2 ^ (n + 1) := by
    rw [actualRoot_orderOf n hn S e, pow_succ, mul_comm]
  have hyh := orderOf_odd_power hy2 hh
  have hak : orderOf (a ^ k) ∣ 2 ^ n := by
    have ha : orderOf a = 2 ^ n := orderOf_wreathModelHom_a n S e
    rw [← ha]
    exact orderOf_pow_dvd k
  have hakpow : ∃ e : ℕ, orderOf (a ^ k) = 2 ^ e := by
    obtain ⟨e', -, he'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hak
    exact ⟨e', he'⟩
  set α := ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
    (basis.representation χ).character (actualRoot S e ^ h) * conj (v χ k 0) with hα
  set β := ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
    (basis.representation χ).character (actualRoot S e ^ h) * conj (v χ k 1) with hβ
  have hcomb : ∀ r ∈ C k, Odd (orderOf r) → α + β * (1 + ε * ΦG r) = 0 := by
    intro r hr hrodd
    have hrc : Commute (a ^ k) r := by
      have hmem : r ∈ Subgroup.centralizer {a ^ k} := hC k ▸ hr
      rw [Subgroup.mem_centralizer_singleton_iff] at hmem
      exact hmem.symm
    have horth := hvan (a ^ k * r) (fun a' c hac hcomm ha' hc hconj => by
      have heq := two_part_unique (g := a ^ k * r) rfl hrc hakpow hrodd hac hcomm ha' hc
      rw [← heq] at hconj
      obtain ⟨c', hc'⟩ := hconj
      have hord := SemiconjBy.orderOf_eq _ hc'
      rw [hyh] at hord
      rw [hord, Nat.pow_dvd_pow_iff_le_right (by norm_num)] at hak
      omega)
    have hexp : ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        (basis.representation χ).character (actualRoot S e ^ h) *
          conj ((basis.representation χ).character (a ^ k * r)) =
        conj (lamG r) * (α + β * (1 + ε * ΦG r)) := by
      rw [hα, hβ, Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun χ hχ => ?_
      rw [hv χ hχ k hk r hr hrodd]
      simp only [map_mul, map_add, map_one, map_intCast, hΦreal]
      ring
    rw [hexp] at horth
    exact (mul_eq_zero.mp horth).resolve_left
      ((map_ne_zero (starRingEnd ℂ)).mpr (hlam0 k hk r hr))
  have hzero := hindep k hk α β hcomb
  obtain rfl | rfl : ℓ = 0 ∨ ℓ = 1 := by fin_cases ℓ <;> simp
  · exact hzero.1
  · exact hzero.2

theorem flat_signed_even_fourier_orthogonal (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (B : basis.index) (v : basis.index → ℕ → Fin 2 → ℂ)
    (hn : 2 ≤ n) {θ : ℂ} (hθ : IsPrimitiveRoot θ (2 * 2 ^ n)) (ζ : ℂ)
    (F : basis.index → ℤ) {j : ℕ} (ℓ : Fin 2)
    (hF : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
      (F χ : ℂ) = fourierTransform (2 ^ n) ζ (fun k => v χ k ℓ) j)
    (hrow : ∀ i ∈ Finset.range (2 ^ n / 2), ∀ k ∈ Finset.Ico 1 (2 ^ n),
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        (basis.representation χ).character (actualRoot S e ^ (2 * i + 1)) *
          conj (v χ k ℓ) = 0)
    (r : ℕ) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
      signedEvenEigenmultiplicity (basis.representation χ) (actualRoot S e) θ (2 ^ n) r * F χ =
        0 := by
  set BB := coefficientBlock basis (localizedComplexIntegerRing ideal) B with hBB
  set y := actualRoot S e with hy
  set M₀ := 2 ^ n / 2 with hM₀
  apply Int.cast_injective (α := ℂ)
  push_cast
  calc ∑ χ ∈ BB, (signedEvenEigenmultiplicity (basis.representation χ) y θ (2 ^ n) r : ℂ) *
        (F χ : ℂ)
      = ∑ χ ∈ BB, ((M₀ : ℂ)⁻¹ * ∑ i ∈ Finset.range M₀,
          (θ ^ 2)⁻¹ ^ (r * (2 * i + 1)) * (basis.representation χ).character (y ^ (2 * i + 1))) *
          conj (((2 ^ n : ℕ) : ℂ)⁻¹ *
            ∑ k ∈ Finset.Ico 1 (2 ^ n), (ζ ^ (j * k) - 1) * v χ k ℓ) := by
        refine Finset.sum_congr rfl fun χ hχ => ?_
        rw [actualRoot_signed_even_inversion n hn S e (basis.representation χ) hθ r]
        congr 1
        rw [← map_intCast (starRingEnd ℂ) (F χ), hF χ hχ]
        rfl
    _ = ∑ χ ∈ BB, ∑ i ∈ Finset.range M₀, ∑ k ∈ Finset.Ico 1 (2 ^ n),
          ((M₀ : ℂ)⁻¹ * ((2 ^ n : ℕ) : ℂ)⁻¹) * ((θ ^ 2)⁻¹ ^ (r * (2 * i + 1)) *
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
          ∑ k ∈ Finset.Ico 1 (2 ^ n), (θ ^ 2)⁻¹ ^ (r * (2 * i + 1)) * conj (ζ ^ (j * k) - 1) *
            ∑ χ ∈ BB, (basis.representation χ).character (y ^ (2 * i + 1)) *
              conj (v χ k ℓ) := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
    _ = 0 := by
        rw [Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun k hk => by
          rw [hrow i hi k hk, mul_zero], mul_zero]

theorem flat_fourier_rows_at_one_eigen (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (B : basis.index)
    (C : ℕ → Subgroup G) (lamG ΦG : G → ℂ) (hlam1 : lamG 1 = 1) (ε : ℤ) (q : ℕ)
    (hq : ΦG 1 = q) (v : basis.index → ℕ → Fin 2 → ℂ)
    (hv : IsTwistedCentralSectionRows basis ideal B (wreathModelHom S e (Original.a (2 ^ n)))
      (2 ^ n) C lamG ΦG ε v)
    {θ : ℂ} (hθ : IsPrimitiveRoot θ (2 * 2 ^ n)) {ζ : ℂ} (hθζ : θ ^ 2 = ζ)
    {χ : basis.index} (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B)
    {j : ℕ} (hj : j ∈ Finset.Ico 1 (2 ^ n)) :
    fourierTransform (2 ^ n) ζ (fun k => v χ k 0) j +
        (1 + ε * q) * fourierTransform (2 ^ n) ζ (fun k => v χ k 1) j =
      (((cyclicEigenmultiplicity (basis.representation χ) (actualRoot S e) θ (2 ^ n - j) : ℤ) +
        cyclicEigenmultiplicity (basis.representation χ) (actualRoot S e) θ (2 * 2 ^ n - j) -
        cyclicEigenmultiplicity (basis.representation χ) (actualRoot S e) θ 0 -
        cyclicEigenmultiplicity (basis.representation χ) (actualRoot S e) θ (2 ^ n) : ℤ) : ℂ) := by
  rw [Finset.mem_Ico] at hj
  set y := actualRoot S e with hy
  have hm : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hy2m : y ^ (2 * 2 ^ n) = 1 := by
    rw [← actualRoot_orderOf n hn S e]
    exact pow_orderOf_eq_one _
  rw [← fourier_character_square_powers (basis.representation χ) y hm hy2m hθ hj.1 hj.2, hθζ]
  have hval : ∀ k ∈ Finset.Ico 1 (2 ^ n), v χ k 0 + (1 + ε * q) * v χ k 1 =
      (basis.representation χ).character (y ^ (2 * k)) := by
    intro k hk
    have h := hv χ hχ k hk 1 (Subgroup.one_mem _) (by rw [orderOf_one]; exact odd_one)
    rw [mul_one, hq, hlam1, one_mul] at h
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

end CFSG.Wreathed.FlatSquareRoot
