module

public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigiditySignedEven

public noncomputable section
namespace CFSG.Wreathed.SquareRootSmallCharacterRigidity
open CFSG.Wreathed CFSG.Wreathed.WreathCentralSquare CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

theorem half_odd_phase_average (m : ℕ) (hm : 0 < m) (heven : Even m)
    (root : ℂ) (hroot : IsPrimitiveRoot root (2 * m)) (r : ℕ) (hr : r < m / 2) :
    ((m / 2 : ℕ) : ℂ)⁻¹ * ∑ k ∈ Finset.range (m / 2),
      (root ^ 2)⁻¹ ^ (r * (2 * k + 1)) = if r = 0 then 1 else 0 := by
  have htwice : 2 * (m / 2) = m := by obtain ⟨a, ha⟩ := heven; omega
  have hhalf : 0 < m / 2 := by omega
  by_cases hzero : r = 0
  · simp only [hzero, Nat.zero_mul, pow_zero, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, ite_true]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hhalf.ne')
  · have hprimitive : IsPrimitiveRoot (root ^ 4) (m / 2) :=
      hroot.pow (by omega) (by omega)
    let u : ℂˣ := Units.mk0 (root ^ 4) (pow_ne_zero _ (hroot.ne_zero (by omega)))
    have hu : (u : ℂ) = root ^ 4 := rfl
    have hsum := primitiveRoot_fourier_sum (m / 2) u hprimitive r hr
    rw [ite_eq_right hzero] at hsum ⊢
    have hphase (k : ℕ) :
        (root ^ 2)⁻¹ ^ (r * (2 * k + 1)) =
          (root ^ 2)⁻¹ ^ r * (↑(u ^ k)⁻¹ : ℂ) ^ r := by
      simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, hu,
        inv_pow, ← pow_mul]
      rw [← mul_inv, ← pow_add]
      congr 2
      ring
    rw [Finset.sum_congr rfl (fun k _ => hphase k), ← Finset.mul_sum, hsum,
      mul_zero, mul_zero]

theorem signed_even_coefficients_of_constant_odd_powers {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (y : G) (m : ℕ) (hm : 0 < m)
    (heven : Even m) (hy : y ^ (2 * m) = 1) (root : ℂ)
    (hroot : IsPrimitiveRoot root (2 * m)) (hconj : IsConj y (y ^ (m + 1)))
    (δ : ℤ) (hvalue : ∀ h : ℕ, Odd h → data.character (y ^ h) = (δ : ℂ)) :
    ∀ r < m / 2, signedEvenEigenmultiplicity data y root m r = if r = 0 then δ else 0 := by
  intro r hr
  have havg := half_odd_power_weighted_average_eigenmultiplicity data y m hm heven
    hy root hroot hconj r
  have hcoeff : (signedEvenEigenmultiplicity data y root m r : ℂ) =
      if r = 0 then (δ : ℂ) else 0 := by
    rw [← havg]
    simp only [hvalue _ (show Odd (2 * _ + 1) from ⟨_, rfl⟩)]
    rw [← Finset.sum_mul, ← mul_assoc, half_odd_phase_average m hm heven root hroot r hr]
    split_ifs <;> simp
  by_cases hzero : r = 0
  · rw [ite_eq_left hzero] at hcoeff ⊢
    exact_mod_cast hcoeff
  · rw [ite_eq_right hzero] at hcoeff ⊢
    exact_mod_cast hcoeff

theorem constant_odd_powers_iff_signed_even_multiplicities {G : Type*} [Group G]
    {data : FiniteComplexRepresentation G} {y : G} (m : ℕ) (hm : 0 < m)
    (heven : Even m) (hy : y ^ (2 * m) = 1) (root : ℂ)
    (hroot : IsPrimitiveRoot root (2 * m)) (hconj : IsConj y (y ^ (m + 1))) {δ : ℤ} :
    (∀ h : ℤ, Odd h → data.character (y ^ h) = (δ : ℂ)) ↔
      signedEvenEigenmultiplicity data y root m 0 = δ ∧
        ∀ r : ℕ, 0 < r → r < m / 2 → signedEvenEigenmultiplicity data y root m r = 0 := by
  have hhalf : 0 < m / 2 := by obtain ⟨a, ha⟩ := heven; omega
  constructor
  · intro hvalue
    have hnatural (h : ℕ) (hh : Odd h) : data.character (y ^ h) = (δ : ℂ) := by
      simpa only [zpow_natCast] using hvalue (h : ℤ) (by exact_mod_cast hh)
    have hcoeff := signed_even_coefficients_of_constant_odd_powers data y m hm heven
      hy root hroot hconj δ hnatural
    refine ⟨by simpa using hcoeff 0 hhalf, ?_⟩
    intro r hr hrange
    simpa only [ite_eq_right hr.ne'] using hcoeff r hrange
  · rintro ⟨hzero, hnonzero⟩ h hh
    rw [signed_even_character_zpow_expansion data y m hm heven hy root hroot hconj h hh,
      Finset.sum_eq_single 0]
    · simp only [hzero, Nat.cast_zero, zero_mul, zpow_zero, mul_one]
    · intro r hr hrzero
      rw [hnonzero r (Nat.pos_of_ne_zero hrzero) (Finset.mem_range.mp hr),
        Int.cast_zero, zero_mul]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hhalf)).elim

theorem minus_one_odd_powers_iff_eigenspace_multiplicities {G : Type*} [Group G]
    {data : FiniteComplexRepresentation G} {y : G} (m : ℕ) (hm : 0 < m)
    (heven : Even m) (hy : y ^ (2 * m) = 1) (root : ℂ)
    (hroot : IsPrimitiveRoot root (2 * m)) (hconj : IsConj y (y ^ (m + 1))) :
    (∀ h : ℤ, Odd h → data.character (y ^ h) = -1) ↔
      cyclicEigenmultiplicity data y root m = cyclicEigenmultiplicity data y root 0 + 1 ∧
        ∀ r : ℕ, 0 < r → r < m / 2 →
          cyclicEigenmultiplicity data y root (2 * r) =
            cyclicEigenmultiplicity data y root (2 * r + m) := by
  have htest := constant_odd_powers_iff_signed_even_multiplicities (data := data) (y := y)
    m hm heven hy root hroot hconj (δ := -1)
  simp only [Int.cast_neg, Int.cast_one] at htest
  rw [htest]
  simp only [signedEvenEigenmultiplicity, Nat.mul_zero, Nat.zero_add]
  constructor
  · rintro ⟨hzero, hnonzero⟩
    refine ⟨by omega, ?_⟩
    intro r hr hrange
    have h := hnonzero r hr hrange
    omega
  · rintro ⟨hzero, hnonzero⟩
    refine ⟨by omega, ?_⟩
    intro r hr hrange
    rw [hnonzero r hr hrange, sub_self]

theorem actual_root_minus_one_iff_eigenspace_multiplicities {G : Type} [Group G]
    {n : ℕ} (hn : 2 ≤ n) {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ n)}
    {data : FiniteComplexRepresentation G} (root : ℂ)
    (hroot : IsPrimitiveRoot root (2 * 2 ^ n)) :
    (∀ h : ℤ, Odd h → data.character (actualRoot S e ^ h) = -1) ↔
      cyclicEigenmultiplicity data (actualRoot S e) root (2 ^ n) =
        cyclicEigenmultiplicity data (actualRoot S e) root 0 + 1 ∧
      ∀ r : ℕ, 0 < r → r < 2 ^ n / 2 →
        cyclicEigenmultiplicity data (actualRoot S e) root (2 * r) =
          cyclicEigenmultiplicity data (actualRoot S e) root (2 * r + 2 ^ n) := by
  have hy : actualRoot S e ^ (2 * 2 ^ n) = 1 := by
    rw [← actualRoot_orderOf n hn S e]
    exact pow_orderOf_eq_one _
  exact minus_one_odd_powers_iff_eigenspace_multiplicities (data := data)
    (y := actualRoot S e) (2 ^ n)
    (pow_pos (by omega) _) (Even.pow_of_ne_zero even_two (by omega)) hy root hroot
    (isConj_iff.mpr ⟨wreathModelHom S e (Original.x2 (2 ^ n)),
      actualRoot_conjugate_half n (by omega) S e⟩)

theorem actual_principal_section_minus_one_iff_eigenspace_multiplicities
    {G : Type} [Group G] [Fintype G]
    {n : ℕ} (hn : 2 ≤ n) {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ n)}
    {basis : FiniteIrreducibleCharacterBasis G} (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    {χ : basis.index}
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (root : ℂ) (hroot : IsPrimitiveRoot root (2 * 2 ^ n)) :
    (∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
      v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
        (basis.representation χ).character (actualRoot S e ^ h * v) = -1) ↔
      cyclicEigenmultiplicity (basis.representation χ) (actualRoot S e) root (2 ^ n) =
        cyclicEigenmultiplicity (basis.representation χ) (actualRoot S e) root 0 + 1 ∧
      ∀ r : ℕ, 0 < r → r < 2 ^ n / 2 →
        cyclicEigenmultiplicity (basis.representation χ) (actualRoot S e) root (2 * r) =
          cyclicEigenmultiplicity (basis.representation χ) (actualRoot S e)
            root (2 * r + 2 ^ n) := by
  rw [← actual_root_minus_one_iff_eigenspace_multiplicities hn
    (S := S) (e := e) (data := basis.representation χ) root hroot]
  constructor
  · intro hvalue h hh
    simpa only [mul_one] using hvalue h 1 hh (by simp) (Subgroup.one_mem _)
  · intro hvalue h v hh hv hcentral
    rw [(actual_root_principal_columns n hn S e basis ideal principal hprincipal h hh).1
      χ hχ v hcentral hv]
    exact hvalue h hh

end CFSG.Wreathed.SquareRootSmallCharacterRigidity
