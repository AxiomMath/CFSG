module

public import CFSG.CharacterTheory.Wreathed.PrincipalSectionColumns
public import CFSG.CharacterTheory.BlockBasics.Sections
public import CFSG.CharacterTheory.Wreathed.ConditionalFourierColumnsIntegrality

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.ConditionalFourier

open CFSG.TwoRankLowerBound.Helpers

variable {G : Type} [Group G] [Fintype G]

omit [Fintype G] in
theorem two_part_unique {g a c a' c' : G} (hg : a * c = g) (hac : Commute a c)
    (ha : ∃ e : ℕ, orderOf a = 2 ^ e) (hc : Odd (orderOf c)) (hg' : a' * c' = g)
    (hac' : Commute a' c') (ha' : ∃ e : ℕ, orderOf a' = 2 ^ e) (hc' : Odd (orderOf c')) :
    a = a' := by
  obtain ⟨e, he⟩ := ha
  obtain ⟨e', he'⟩ := ha'
  have hcop : Nat.Coprime (orderOf a) (orderOf c) := by
    rw [he]
    exact (Nat.coprime_two_left.mpr hc).pow_left e
  have hcop' : Nat.Coprime (orderOf a') (orderOf c') := by
    rw [he']
    exact (Nat.coprime_two_left.mpr hc').pow_left e'
  obtain ⟨x, hx⟩ :=
    CFSG.BlockSectionOrthogonality.Helpers.primaryPart_eq_power_of_coprime_factors hg hac hcop
  obtain ⟨x', hx'⟩ :=
    CFSG.BlockSectionOrthogonality.Helpers.primaryPart_eq_power_of_coprime_factors hg' hac' hcop'
  have hcg : ∃ y : ℕ, g ^ y = c := by
    obtain ⟨y, hy⟩ := CFSG.BlockSectionOrthogonality.Helpers.primaryPart_eq_power_of_coprime_factors
      (show c * a = g by rw [← hac.eq, hg]) hac.symm hcop.symm
    exact ⟨y, hy⟩
  have hcg' : ∃ y : ℕ, g ^ y = c' := by
    obtain ⟨y, hy⟩ := CFSG.BlockSectionOrthogonality.Helpers.primaryPart_eq_power_of_coprime_factors
      (show c' * a' = g by rw [← hac'.eq, hg']) hac'.symm hcop'.symm
    exact ⟨y, hy⟩
  obtain ⟨y, hy⟩ := hcg
  obtain ⟨y', hy'⟩ := hcg'
  have hcomm₁ : Commute a a' := by rw [← hx, ← hx']; exact Commute.pow_pow_self g x x'
  have hcomm₂ : Commute c c' := by rw [← hy, ← hy']; exact Commute.pow_pow_self g y y'
  have heq : a⁻¹ * a' = c * c'⁻¹ := by
    have h : a * c = a' * c' := hg.trans hg'.symm
    calc a⁻¹ * a' = a⁻¹ * a' * c' * c'⁻¹ := by group
      _ = a⁻¹ * (a' * c') * c'⁻¹ := by group
      _ = a⁻¹ * (a * c) * c'⁻¹ := by rw [h]
      _ = c * c'⁻¹ := by group
  have ha1 : a ^ 2 ^ (e + e') = 1 := by
    rw [pow_add, pow_mul, ← he, pow_orderOf_eq_one, one_pow]
  have ha1' : a' ^ 2 ^ (e + e') = 1 := by
    rw [add_comm, pow_add, pow_mul, ← he', pow_orderOf_eq_one, one_pow]
  have h2 : orderOf (a⁻¹ * a') ∣ 2 ^ (e + e') := by
    apply orderOf_dvd_of_pow_eq_one
    rw [(hcomm₁.inv_left).mul_pow, inv_pow, ha1, ha1', inv_one, one_mul]
  have hodd : Odd (orderOf (c * c'⁻¹)) := by
    have hd : orderOf (c * c'⁻¹) ∣ orderOf c * orderOf c' := by
      apply orderOf_dvd_of_pow_eq_one
      rw [(hcomm₂.inv_right).mul_pow, pow_mul, pow_orderOf_eq_one, one_pow, one_mul, mul_comm,
        pow_mul, inv_pow, pow_orderOf_eq_one, inv_one, one_pow]
    exact Odd.of_dvd_nat (hc.mul hc') hd
  rw [heq] at h2
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have hk0 : k = 0 := by
    by_contra hk0
    rw [hk] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hk0⟩)
  rw [hk0, pow_zero, orderOf_eq_one_iff, ← heq] at hk
  have := congrArg (a * ·) hk
  simp only [mul_inv_cancel_left, mul_one] at this
  exact this.symm

theorem exists_regular_rows {C : Type} [Group C] [Fintype C]
    (localBasis : FiniteIrreducibleCharacterBasis C) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] {localPrincipal : localBasis.index} {Φ : C → ℂ} {ε : ℤ} {q : ℕ}
    {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hdata : PrincipalRegularIntegralBasisData localBasis ideal localPrincipal Φ ε q M) :
    ∃ d : localBasis.index → Fin 2 → ℤ,
      (∀ θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
        ∀ y : C, Odd (orderOf y) →
          (localBasis.representation θ).character y = d θ 0 + d θ 1 * (1 + ε * Φ y)) ∧
      ∀ j k, ∑ θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal)
        localPrincipal, d θ j * d θ k = M j k := by
  obtain ⟨D, hD⟩ := hdata.rows
  have hgram := hdata.gram D hD
  let d : localBasis.index → Fin 2 → ℤ := fun θ j =>
    if hθ : θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal
    then D ⟨θ, hθ⟩ j else 0
  refine ⟨d, fun θ hθ y hy => ?_, fun j k => ?_⟩
  · have h := congrFun (hD ⟨θ, hθ⟩) ⟨y, hy⟩
    simp only [oddRestriction, Pi.add_apply, Pi.smul_apply, Pi.one_apply, zsmul_eq_mul,
      smul_eq_mul, Pi.mul_apply, Pi.intCast_apply] at h
    simp only [d, dite_eq_left hθ]
    rw [h]
    ring
  · have h := congrFun (congrFun hgram j) k
    rw [Matrix.mul_apply] at h
    simp only [Matrix.transpose_apply] at h
    rw [← h, ← Finset.sum_coe_sort (coefficientBlock localBasis (localizedComplexIntegerRing ideal)
      localPrincipal)]
    refine Finset.sum_congr rfl fun θ _ => ?_
    simp only [d, dite_eq_left θ.2]

theorem section_rows_of_regular_basis (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {u : G} {r : ℕ}
    (hr : 1 ≤ r) (hu : orderOf u = 2 ^ r) (C : Subgroup G)
    (hC : C = Subgroup.centralizer (Subgroup.zpowers u : Set G))
    (localBasis : FiniteIrreducibleCharacterBasis C) (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 ^ r)) {Φ : C → ℂ} {ε : ℤ} {q : ℕ}
    {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hdata : PrincipalRegularIntegralBasisData localBasis ideal localPrincipal Φ ε q M) :
    ∃ v : basis.index → Fin 2 → ℂ,
      (∀ χ ℓ, v χ ℓ ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)) ∧
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        ∀ y : C, Odd (orderOf y) →
          (basis.representation χ).character (u * y) = v χ 0 + v χ 1 * (1 + ε * Φ y)) ∧
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        ∀ w : Fin 2 → ℂ, (∀ y : C, Odd (orderOf y) →
          (basis.representation χ).character (u * y) = w 0 + w 1 * (1 + ε * Φ y)) →
            w = v χ) ∧
      (∀ ℓ t, ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        conj (v χ ℓ) * v χ t = M ℓ t) ∧
      ∀ g : G, (∀ a c : G, a * c = g → Commute a c → (∃ e : ℕ, orderOf a = 2 ^ e) →
          Odd (orderOf c) → ¬ IsConj a u) →
        ∀ ℓ, ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          v χ ℓ * conj ((basis.representation χ).character g) = 0 := by
  subst hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd_iff : ∀ n : ℕ, ¬ 2 ∣ n ↔ Odd n := fun n => by
    rw [Nat.odd_iff, Nat.two_dvd_ne_zero]
  obtain ⟨l, hlB0, hlΦ⟩ := hdata.irreducible
  let b : Fin 2 → Subgroup.centralizer (Subgroup.zpowers u : Set G) → ℂ := ![1, 1 + (ε : ℂ) • Φ]
  have hb0 : ∀ y, b 0 y = 1 := fun y => rfl
  have hb1 : ∀ y, b 1 y = 1 + ε * Φ y := fun y => rfl
  have hbmem : ∀ j, ∃ c : localBasis.index → ℂ, ∀ y, ¬ 2 ∣ orderOf y →
      b j y = ∑ θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal)
        localPrincipal, c θ * (localBasis.representation θ).character y := by
    have hPB0 := coefficientBlock_self_mem localBasis (localizedComplexIntegerRing ideal)
      localPrincipal
    intro j
    fin_cases j
    · refine ⟨fun θ => if θ = localPrincipal then 1 else 0, fun y _ => ?_⟩
      show (1 : ℂ) = ∑ θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal)
        localPrincipal, (if θ = localPrincipal then (1 : ℂ) else 0) *
          (localBasis.representation θ).character y
      simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq' _ localPrincipal, ite_eq_left hPB0, hlocalPrincipal]
      rfl
    · refine ⟨fun θ => (if θ = localPrincipal then 1 else 0) + (if θ = l then (ε : ℂ) else 0),
        fun y _ => ?_⟩
      show (1 : ℂ) + ε * Φ y = ∑ θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal)
        localPrincipal, ((if θ = localPrincipal then (1 : ℂ) else 0) +
          (if θ = l then (ε : ℂ) else 0)) * (localBasis.representation θ).character y
      simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq' _ localPrincipal, Finset.sum_ite_eq' _ l, ite_eq_left hPB0,
        ite_eq_left hlB0, hlocalPrincipal, hlΦ]
      rfl
  have hbindep : ∀ c : Fin 2 → ℂ, (∀ y, ¬ 2 ∣ orderOf y → ∑ j, c j * b j y = 0) → c = 0 := by
    intro c hc
    obtain ⟨h0, h1⟩ := eq_zero_of_odd_combination Φ ε q hdata.degree hdata.linearIndependent
      (α := c 0) (β := c 1) (fun y hy => by
        have h := hc y ((hodd_iff _).mpr hy)
        rw [Fin.sum_univ_two, hb0, hb1, mul_one] at h
        exact h)
    funext j
    fin_cases j
    · exact h0
    · exact h1
  obtain ⟨d, hd, hdgram⟩ := exists_regular_rows localBasis ideal hdata
  have hd' : ∀ θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
      ∀ y, ¬ 2 ∣ orderOf y →
        (localBasis.representation θ).character y = ∑ j, (d θ j : ℂ) * b j y := by
    intro θ hθ y hy
    rw [hd θ hθ y ((hodd_iff _).mp hy), Fin.sum_univ_two, hb0, hb1, mul_one]
  obtain ⟨U, -, -, -, -, -, hUint, hrow, huniq, hgram, hvanish⟩ :=
    principal_primary_section_cyclotomic_basis_columns basis ideal 2 principal hprincipal hr hu
      localBasis localPrincipal hlocalPrincipal hζ 2 (by norm_num) b hbmem hbindep d hd'
  refine ⟨U, hUint, fun χ hχ y hy => ?_, fun χ hχ w hw => ?_, fun ℓ t => ?_, fun g hg ℓ => ?_⟩
  · rw [hrow χ hχ y ((hodd_iff _).mpr hy), Fin.sum_univ_two, hb0, hb1, mul_one]
  · apply huniq χ hχ w
    intro y hy
    rw [hw y ((hodd_iff _).mp hy), Fin.sum_univ_two, hb0, hb1, mul_one]
  · rw [hgram ℓ t]
    push_cast
    rw [← hdgram ℓ t]
    push_cast
    rfl
  · refine hvanish g (fun a c hac hcomm ha hc => hg a c hac hcomm ha ((hodd_iff _).mp hc)) ℓ

@[expose] def IsCentralSectionRows (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (principal : basis.index)
    (a : G) (m : ℕ) (C : ℕ → Subgroup G) (Φ : G → ℂ) (ε : ℤ)
    (v : basis.index → ℕ → Fin 2 → ℂ) : Prop :=
  ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
    ∀ k ∈ Finset.Ico 1 m, ∀ r ∈ C k, Odd (orderOf r) →
      (basis.representation χ).character (a ^ k * r) = v χ k 0 + v χ k 1 * (1 + ε * Φ r)

theorem isPrimitiveRoot_pow_div {ζ : ℂ} {m d : ℕ} (hζ : IsPrimitiveRoot ζ m) (hm0 : 0 < m)
    (hd : d ∣ m) (hd0 : 0 < d) : IsPrimitiveRoot (ζ ^ (m / d)) d := by
  obtain ⟨c, rfl⟩ := hd
  rw [Nat.mul_div_cancel_left c hd0]
  exact hζ.pow hm0 (mul_comm d c)

theorem section_rows_family (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {a : G} {m : ℕ}
    (hm : orderOf a = m) (hm2 : ∃ n : ℕ, m = 2 ^ n) (C : ℕ → Subgroup G)
    (hC : ∀ k, C k = Subgroup.centralizer {a ^ k}) (Φ : G → ℂ)
    (hΦreal : ∀ g, conj (Φ g) = Φ g) (ε : ℤ) (q : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hdata : ∀ k ∈ Finset.Ico 1 m, ∀ (localBasis : FiniteIrreducibleCharacterBasis (C k))
      (localPrincipal : localBasis.index),
      (localBasis.representation localPrincipal).character = 1 →
        PrincipalRegularIntegralBasisData localBasis ideal localPrincipal (fun c => Φ c) ε q M)
    (hnonconj : ∀ k ∈ Finset.Ico 1 m, ∀ h ∈ Finset.Ico 1 m, IsConj (a ^ k) (a ^ h) → k = h)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) :
    ∃ v : basis.index → ℕ → Fin 2 → ℂ,
      (∀ χ, ∀ k ∈ Finset.Ico 1 m, ∀ ℓ, v χ k ℓ ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)) ∧
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        ∀ k ∈ Finset.Ico 1 m, ∀ r : C k, Odd (orderOf r) →
          (basis.representation χ).character (a ^ k * r) = v χ k 0 + v χ k 1 * (1 + ε * Φ r)) ∧
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        ∀ k ∈ Finset.Ico 1 m, ∀ w : Fin 2 → ℂ, (∀ r : C k, Odd (orderOf r) →
          (basis.representation χ).character (a ^ k * r) = w 0 + w 1 * (1 + ε * Φ r)) →
            w = v χ k) ∧
      (∀ k ∈ Finset.Ico 1 m, ∀ h ∈ Finset.Ico 1 m, ∀ ℓ t,
        ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          conj (v χ k ℓ) * v χ h t = if k = h then (M ℓ t : ℂ) else 0) ∧
      (∀ k ∈ Finset.Ico 1 m, ∀ ℓ,
        ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          (basis.representation χ).character 1 * v χ k ℓ = 0) := by
  classical
  obtain ⟨n, rfl⟩ := hm2
  have hord : ∀ k ∈ Finset.Ico 1 (2 ^ n), ∃ r : ℕ, 1 ≤ r ∧ orderOf (a ^ k) = 2 ^ r := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hdvd : orderOf (a ^ k) ∣ 2 ^ n := by
      rw [← hm]
      exact orderOf_pow_dvd k
    obtain ⟨r, -, hr⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    refine ⟨r, ?_, hr⟩
    by_contra hr0
    have : r = 0 := by omega
    rw [this, pow_zero, orderOf_eq_one_iff] at hr
    have := orderOf_dvd_of_pow_eq_one hr
    rw [hm] at this
    exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  have hlocal : ∀ k ∈ Finset.Ico 1 (2 ^ n), ∃ (localBasis : FiniteIrreducibleCharacterBasis (C k))
      (localPrincipal : localBasis.index),
      (localBasis.representation localPrincipal).character = 1 := by
    intro k _
    obtain ⟨lb⟩ := finiteIrreducibleCharacterBasis_exists (G := C k)
    obtain ⟨l0, hl0⟩ := finiteIrreducibleCharacterBasis_contains_irreducible lb
      (principalFiniteComplexRepresentation (C k))
      (principalFiniteComplexRepresentation_isIrreducible _)
    rw [principalFiniteComplexRepresentation_character] at hl0
    exact ⟨lb, l0, hl0⟩
  have hrows : ∀ k ∈ Finset.Ico 1 (2 ^ n), ∃ w : basis.index → Fin 2 → ℂ,
      (∀ χ ℓ, w χ ℓ ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)) ∧
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        ∀ y : C k, Odd (orderOf y) →
          (basis.representation χ).character (a ^ k * y) = w χ 0 + w χ 1 * (1 + ε * Φ y)) ∧
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        ∀ w' : Fin 2 → ℂ, (∀ y : C k, Odd (orderOf y) →
          (basis.representation χ).character (a ^ k * y) = w' 0 + w' 1 * (1 + ε * Φ y)) →
            w' = w χ) ∧
      (∀ ℓ t, ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        conj (w χ ℓ) * w χ t = M ℓ t) ∧
      (∀ g : G, (∀ a' c : G, a' * c = g → Commute a' c → (∃ e : ℕ, orderOf a' = 2 ^ e) →
          Odd (orderOf c) → ¬ IsConj a' (a ^ k)) →
        ∀ ℓ, ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          w χ ℓ * conj ((basis.representation χ).character g) = 0) := by
    intro k hk
    obtain ⟨r, hr1, hr⟩ := hord k hk
    obtain ⟨lb, l0, hl0⟩ := hlocal k hk
    have hdvd : 2 ^ r ∣ 2 ^ n := by
      rw [← hr, ← hm]
      exact orderOf_pow_dvd k
    have hζk := isPrimitiveRoot_pow_div hζ (by positivity) hdvd (by positivity)
    obtain ⟨w, hw1, hw2, hw3, hw4, hw5⟩ := section_rows_of_regular_basis basis ideal principal
      hprincipal hr1 hr (C k)
      (by rw [hC k, ← CFSG.BlockBasics.centralizer_zpowers_eq_centralizer_singleton])
      lb l0 hl0 hζk (hdata k hk lb l0 hl0)
    refine ⟨w, fun χ ℓ => ?_, hw2, hw3, hw4, hw5⟩
    have hle : Algebra.adjoin ℤ ({ζ ^ (2 ^ n / 2 ^ r)} : Set ℂ) ≤
        Algebra.adjoin ℤ ({ζ} : Set ℂ) := by
      apply Algebra.adjoin_le
      rw [Set.singleton_subset_iff]
      exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton ζ)) _
    exact hle (hw1 χ ℓ)
  choose! w hw1 hw2 hw3 hw4 hw5 using hrows
  refine ⟨fun χ k ℓ => w k χ ℓ, fun χ k hk ℓ => hw1 k hk χ ℓ, fun χ hχ k hk r hr =>
    hw2 k hk χ hχ r hr, fun χ hχ k hk w' hw' => hw3 k hk χ hχ w' hw', ?_, ?_⟩
  · intro k hk h hh ℓ t
    by_cases hkh : k = h
    · subst hkh
      rw [ite_eq_left rfl]
      exact hw4 k hk ℓ t
    · rw [ite_eq_right hkh]
      obtain ⟨lb, l0, hl0⟩ := hlocal h hh
      have hvan : ∀ r : C h, Odd (orderOf r) → ∀ ℓ',
          ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
            w k χ ℓ' * conj ((basis.representation χ).character (a ^ h * r)) = 0 := by
        intro r hr ℓ'
        apply hw5 k hk
        intro a' c hac hcomm ha' hc hconj
        have hrc : Commute (a ^ h) (r : G) := by
          have hmem : (r : G) ∈ Subgroup.centralizer {a ^ h} := hC h ▸ r.2
          rw [Subgroup.mem_centralizer_singleton_iff] at hmem
          exact hmem.symm
        have hpow : ∃ e : ℕ, orderOf (a ^ h) = 2 ^ e := by
          obtain ⟨e, -, he⟩ := hord h hh
          exact ⟨e, he⟩
        have hr' : Odd (orderOf (r : G)) := by rwa [Subgroup.orderOf_coe]
        have heq := two_part_unique (g := a ^ h * (r : G)) rfl hrc hpow hr' hac hcomm ha' hc
        rw [← heq] at hconj
        exact hkh (hnonconj k hk h hh hconj.symm)
      have hdata' := hdata h hh lb l0 hl0
      obtain ⟨h0, h1⟩ := eq_zero_of_odd_combination (fun c : C h => Φ c) ε q hdata'.degree
        hdata'.linearIndependent
        (α := ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          w k χ ℓ * conj (w h χ 0))
        (β := ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          w k χ ℓ * conj (w h χ 1)) (fun y hy => by
          have h' := hvan y hy ℓ
          rw [← h']
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun χ hχ => ?_
          rw [hw2 h hh χ hχ y hy, map_add, map_mul, map_add, map_one, map_mul, hΦreal,
            map_intCast]
          ring)
      have htarget : ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          conj (w k χ ℓ) * w h χ t = conj (∑ χ ∈ coefficientBlock basis
            (localizedComplexIntegerRing ideal) principal, w k χ ℓ * conj (w h χ t)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [map_mul, Complex.conj_conj]
      rw [htarget]
      fin_cases t
      · simp only [Fin.zero_eta]
        rw [h0, map_zero]
      · simp only [Fin.mk_one]
        rw [h1, map_zero]
  · intro k hk ℓ
    have h' := hw5 k hk 1 (by
      intro a' c hac hcomm ha' hc hconj
      have heq := two_part_unique (show (1 : G) * 1 = 1 from mul_one 1) (Commute.one_left 1)
        ⟨0, by rw [orderOf_one, pow_zero]⟩ (by rw [orderOf_one]; exact odd_one) hac hcomm ha' hc
      rw [← heq] at hconj
      have h1 := isConj_one_right.mp hconj
      obtain ⟨r, hr1, hr⟩ := hord k hk
      rw [h1, orderOf_one] at hr
      have : (2 : ℕ) ^ r ≠ 1 := Nat.one_lt_two_pow (by omega) |>.ne'
      exact this hr.symm) ℓ
    rw [← h']
    refine Finset.sum_congr rfl fun χ _ => ?_
    have hreal : conj ((basis.representation χ).character 1) =
        (basis.representation χ).character 1 := by
      have h1 : (basis.representation χ).character 1 =
          (Module.finrank ℂ (basis.representation χ).vector : ℂ) := Representation.char_one _
      rw [h1, Complex.conj_natCast]
    rw [hreal]
    ring

end CFSG.Wreathed.ConditionalFourier
