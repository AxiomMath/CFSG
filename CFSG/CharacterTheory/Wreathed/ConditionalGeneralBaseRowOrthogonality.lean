module

public import CFSG.CharacterTheory.Wreathed.ConditionalFourierColumnsSections

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.ConditionalGeneralBase

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.ConditionalFourier

variable {G : Type} [Group G] [Fintype G]

theorem rows_orthogonal_of_section (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (principal : basis.index)
    (a : G) (m : ℕ) (C : ℕ → Subgroup G) (Φ : G → ℂ) (hΦreal : ∀ g, conj (Φ g) = Φ g) (ε : ℤ)
    (q : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hdata : ∀ k ∈ Finset.Ico 1 m, ∀ (localBasis : FiniteIrreducibleCharacterBasis (C k))
      (localPrincipal : localBasis.index),
      (localBasis.representation localPrincipal).character = 1 →
        PrincipalRegularIntegralBasisData localBasis ideal localPrincipal (fun c => Φ c) ε q M)
    (v : basis.index → ℕ → Fin 2 → ℂ) (hv : IsCentralSectionRows basis ideal principal a m C Φ ε v)
    (W : basis.index → ℂ) {k : ℕ} (hk : k ∈ Finset.Ico 1 m)
    (hoff : ∀ r ∈ C k, Odd (orderOf r) →
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        W χ * conj ((basis.representation χ).character (a ^ k * r)) = 0) (ℓ : Fin 2) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      W χ * conj (v χ k ℓ) = 0 := by
  set B₀ := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB₀
  obtain ⟨lb⟩ := finiteIrreducibleCharacterBasis_exists (G := C k)
  obtain ⟨l0, hl0⟩ := finiteIrreducibleCharacterBasis_contains_irreducible lb
    (principalFiniteComplexRepresentation _) (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hl0
  have hreg := hdata k hk lb l0 hl0
  set α := ∑ χ ∈ B₀, W χ * conj (v χ k 0) with hα
  set β := ∑ χ ∈ B₀, W χ * conj (v χ k 1) with hβ
  have hcomb : ∀ r : C k, Odd (orderOf r) → α + β * (1 + ε * Φ r) = 0 := by
    intro r hr
    have hrodd : Odd (orderOf (r : G)) := by rwa [Subgroup.orderOf_coe]
    rw [← hoff r r.2 hrodd, hα, hβ, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [hv χ hχ k hk r r.2 hrodd]
    simp only [map_add, map_mul, map_one, map_intCast, hΦreal]
    ring
  have hzero := eq_zero_of_odd_combination (fun c : C k => Φ c) ε q hreg.degree
    hreg.linearIndependent hcomb
  obtain rfl | rfl : ℓ = 0 ∨ ℓ = 1 := by fin_cases ℓ <;> simp
  · exact hzero.1
  · exact hzero.2

theorem odd_column_rows_orthogonal (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index) (a : G) (m : ℕ)
    (ham : orderOf a = m) (hm2 : ∃ e : ℕ, m = 2 ^ e) (C : ℕ → Subgroup G)
    (hC : ∀ k, C k = Subgroup.centralizer {a ^ k}) (Φ : G → ℂ)
    (hΦreal : ∀ g, conj (Φ g) = Φ g) (ε : ℤ) (q : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hdata : ∀ k ∈ Finset.Ico 1 m, ∀ (localBasis : FiniteIrreducibleCharacterBasis (C k))
      (localPrincipal : localBasis.index),
      (localBasis.representation localPrincipal).character = 1 →
        PrincipalRegularIntegralBasisData localBasis ideal localPrincipal (fun c => Φ c) ε q M)
    (v : basis.index → ℕ → Fin 2 → ℂ) (hv : IsCentralSectionRows basis ideal principal a m C Φ ε v)
    {z : G} (hz : Odd (orderOf z)) {k : ℕ} (hk : k ∈ Finset.Ico 1 m) (ℓ : Fin 2) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character z * conj (v χ k ℓ) = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, he⟩ := hm2
  have hk' := Finset.mem_Ico.mp hk
  refine rows_orthogonal_of_section basis ideal principal a m C Φ hΦreal ε q M hdata v hv
    (fun χ => (basis.representation χ).character z) hk (fun r hr hrodd => ?_) ℓ
  have hrc : Commute (a ^ k) r := by
    rw [hC k, Subgroup.mem_centralizer_singleton_iff] at hr
    exact hr.symm
  have hak : a ^ k ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
  have h := coefficientBlock_section_column_orthogonality basis ideal 2 principal 1 (a ^ k) z r 0 e
    (by rw [orderOf_one]; exact one_dvd _)
    (by rw [← he, ← ham]; exact orderOf_pow_dvd k)
    (Nat.coprime_two_left.mpr hz) (Nat.coprime_two_left.mpr hrodd) (Commute.one_left z) hrc
    (fun hc => hak (isConj_one_right.mp hc))
  rw [← h]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [one_mul, finite_character_conjugate_inverse]

theorem central_combination_gram {ι : Type*} (B : Finset ι) {m : ℕ} (hm : 2 ∣ m)
    (v : ι → ℕ → Fin 2 → ℂ)
    (hvgram : ∀ k ∈ Finset.Ico 1 m, ∀ h ∈ Finset.Ico 1 m, ∀ ℓ t,
      ∑ χ ∈ B, conj (v χ k ℓ) * v χ h t =
        if k = h then (((m : ℤ) • !![4, -2; -2, ((m / 2 + 1 : ℕ) : ℤ)]) ℓ t : ℂ) else 0)
    {k h : ℕ} (hk : k ∈ Finset.Ico 1 m) (hh : h ∈ Finset.Ico 1 m) :
    (∑ χ ∈ B, (v χ k 0 + 2 * v χ k 1) * conj (v χ h 0 + 2 * v χ h 1) =
        if k = h then 2 * (m : ℂ) ^ 2 else 0) ∧
      ∑ χ ∈ B, (v χ k 0 + 2 * v χ k 1) * conj (v χ h 0) = 0 := by
  have hG : ∀ ℓ t, ∑ χ ∈ B, v χ k ℓ * conj (v χ h t) =
      if k = h then (((m : ℤ) • !![4, -2; -2, ((m / 2 + 1 : ℕ) : ℤ)]) ℓ t : ℂ) else 0 := by
    intro ℓ t
    have h' := congrArg (starRingEnd ℂ) (hvgram k hk h hh ℓ t)
    rw [map_sum] at h'
    simp only [map_mul, Complex.conj_conj] at h'
    rw [h']
    split_ifs <;> simp
  have hm2 : (((m : ℤ) / 2 : ℤ) : ℂ) * 2 = m := by
    have h2 := Int.ediv_mul_cancel (show (2 : ℤ) ∣ m by exact_mod_cast hm)
    exact_mod_cast h2
  have h1 : ∑ χ ∈ B, (v χ k 0 + 2 * v χ k 1) * conj (v χ h 0 + 2 * v χ h 1) =
      ∑ χ ∈ B, v χ k 0 * conj (v χ h 0) + 2 * ∑ χ ∈ B, v χ k 0 * conj (v χ h 1) +
        2 * ∑ χ ∈ B, v χ k 1 * conj (v χ h 0) + 4 * ∑ χ ∈ B, v χ k 1 * conj (v χ h 1) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun χ _ => ?_
    simp only [map_add, map_mul, map_ofNat]
    ring
  have h2 : ∑ χ ∈ B, (v χ k 0 + 2 * v χ k 1) * conj (v χ h 0) =
      ∑ χ ∈ B, v χ k 0 * conj (v χ h 0) + 2 * ∑ χ ∈ B, v χ k 1 * conj (v χ h 0) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun χ _ => by ring
  rw [h1, h2, hG, hG, hG, hG]
  by_cases hkh : k = h
  · simp only [hkh, ↓reduceIte, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      smul_eq_mul]
    push_cast
    constructor
    · linear_combination (2 * (m : ℂ)) * hm2
    · ring
  · simp only [hkh, ↓reduceIte]
    norm_num

theorem column_orthogonal_signed_even (basis : FiniteIrreducibleCharacterBasis G)
    (B : Finset basis.index) (W : basis.index → ℂ) (y : G) (ζ : ℂ) (M₀ : ℕ)
    (c : basis.index → ℕ → ℤ)
    (hW : ∀ h : ℤ, Odd h → ∑ χ ∈ B, W χ * conj ((basis.representation χ).character (y ^ h)) = 0)
    (hinv : ∀ χ ∈ B, ∀ r < M₀, (c χ r : ℂ) = (M₀ : ℂ)⁻¹ * ∑ i ∈ Finset.range M₀,
      (basis.representation χ).character (y ^ (2 * i + 1)) * ζ ^ (-((r : ℤ) * (2 * i + 1))))
    {r : ℕ} (hr : r < M₀) : ∑ χ ∈ B, W χ * (c χ r : ℂ) = 0 := by
  have hrow : ∀ i ∈ Finset.range M₀,
      ∑ χ ∈ B, W χ * conj ((basis.representation χ).character (y ^ (2 * i + 1))) = 0 := by
    intro i _
    have h := hW (2 * i + 1 : ℕ) ⟨i, by push_cast; ring⟩
    simpa only [zpow_natCast] using h
  calc ∑ χ ∈ B, W χ * (c χ r : ℂ) = ∑ χ ∈ B, W χ * conj (c χ r : ℂ) :=
        Finset.sum_congr rfl fun χ _ => by rw [map_intCast]
    _ = ∑ χ ∈ B, ∑ i ∈ Finset.range M₀, conj ((M₀ : ℂ)⁻¹ * ζ ^ (-((r : ℤ) * (2 * i + 1)))) *
          (W χ * conj ((basis.representation χ).character (y ^ (2 * i + 1)))) := by
        refine Finset.sum_congr rfl fun χ hχ => ?_
        rw [hinv χ hχ r hr, map_mul, map_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, map_mul]
        ring
    _ = ∑ i ∈ Finset.range M₀, conj ((M₀ : ℂ)⁻¹ * ζ ^ (-((r : ℤ) * (2 * i + 1)))) *
          ∑ χ ∈ B, W χ * conj ((basis.representation χ).character (y ^ (2 * i + 1))) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    _ = 0 := Finset.sum_eq_zero fun i hi => by rw [hrow i hi, mul_zero]

end CFSG.Wreathed.ConditionalGeneralBase
