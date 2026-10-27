module

public import CFSG.CharacterTheory.Wreathed.ConditionalSquareRootSections
public import CFSG.CharacterTheory.Wreathed.ConditionalSquareRootAlgebra
public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityConstantValues
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.ConditionalSquareRoot

open CFSG.Wreathed CFSG.Wreathed.WreathCentralSquare CFSG.Wreathed.SquareRootSmallCharacterRigidity
  CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal

theorem actualRoot_isConj_pow_succ {G : Type} [Group G] (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) : IsConj (actualRoot S e) (actualRoot S e ^ (2 ^ n + 1)) :=
  isConj_iff.mpr ⟨wreathModelHom S e (Original.x2 (2 ^ n)), actualRoot_conjugate_half n hn S e⟩

theorem actualRoot_signed_even_inversion {G : Type} [Group G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (data : FiniteComplexRepresentation G) {η : ℂ}
    (hη : IsPrimitiveRoot η (2 * 2 ^ n)) (r : ℕ) :
    (signedEvenEigenmultiplicity data (actualRoot S e) η (2 ^ n) r : ℂ) =
      ((2 ^ n / 2 : ℕ) : ℂ)⁻¹ * ∑ i ∈ Finset.range (2 ^ n / 2),
        (η ^ 2)⁻¹ ^ (r * (2 * i + 1)) * data.character (actualRoot S e ^ (2 * i + 1)) :=
  (actual_root_signed_even_average n hn S e data η hη r).symm

theorem actualRoot_odd_columns_gram {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    {i i' : ℕ} (hi : i < 2 ^ n / 2) (hi' : i' < 2 ^ n / 2) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character (actualRoot S e ^ (2 * i + 1)) *
        conj ((basis.representation χ).character (actualRoot S e ^ (2 * i' + 1))) =
      if i = i' then (4 * (2 ^ n / 2 : ℕ) : ℂ) else 0 := by
  have hm2 : 2 * (2 ^ n / 2) = 2 ^ n := by
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [hk, pow_succ, Nat.mul_div_cancel _ (by norm_num), mul_comm]
  have hodd : ∀ j : ℕ, Odd ((2 * j + 1 : ℕ) : ℤ) := fun j => ⟨j, by push_cast; ring⟩
  have hz : ∀ j : ℕ, actualRoot S e ^ (2 * j + 1) = actualRoot S e ^ ((2 * j + 1 : ℕ) : ℤ) :=
    fun j => (zpow_natCast _ _).symm
  split_ifs with hii
  · subst hii
    have h := (actual_root_principal_columns n hn S e basis ideal principal hprincipal _
      (hodd i)).2.1
    rw [← hz] at h
    have hnum : (2 * 2 ^ n : ℕ) = 4 * (2 ^ n / 2) := by omega
    rw [Finset.sum_congr rfl fun χ _ => mul_comm _ _, h, hnum]
    push_cast
    ring
  · rw [hz, hz]
    refine actualRoot_odd_power_columns_orthogonal n hn S e basis ideal principal hprincipal
      (hodd i) (hodd i') ?_
    intro hmod
    have hmod' : (2 * i + 1) % 2 ^ n = (2 * i' + 1) % 2 ^ n := by
      have h1 : (((2 * i + 1) % 2 ^ n : ℕ) : ℤ) = (((2 * i' + 1) % 2 ^ n : ℕ) : ℤ) := by
        rw [Int.natCast_mod, Int.natCast_mod]
        exact hmod
      exact_mod_cast h1
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod'
    exact hii (by omega)

theorem actualRoot_signed_even_columns {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    {η : ℂ} (hη : IsPrimitiveRoot η (2 * 2 ^ n)) :
    let M₀ := 2 ^ n / 2
    let y := actualRoot S e
    let B₀ := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    let c : basis.index → ℕ → ℤ := fun χ r =>
      signedEvenEigenmultiplicity (basis.representation χ) y η (2 ^ n) r
    (∀ χ ∈ B₀, ∀ h : ℤ, Odd h → ∀ z ∈ Subgroup.centralizer ({y} : Set G), Odd (orderOf z) →
      (basis.representation χ).character (y ^ h * z) = (basis.representation χ).character (y ^ h) ∧
      (basis.representation χ).character (y ^ h) =
        ∑ r ∈ Finset.range M₀, (c χ r : ℂ) * (η ^ 2) ^ ((r : ℤ) * h)) ∧
    (∀ r < M₀, ∀ t < M₀, ∑ χ ∈ B₀, c χ r * c χ t = if r = t then 4 else 0) ∧
    (∀ r < M₀, ∑ χ ∈ B₀, (c χ r : ℂ) * (basis.representation χ).character 1 = 0) ∧
    c principal 0 = 1 ∧ (∀ r, 0 < r → r < M₀ → c principal r = 0) ∧
    ∀ r < M₀, (B₀.filter (fun χ => c χ r ≠ 0)).card = 4 ∧
      ∀ χ ∈ B₀, c χ r = 0 ∨ c χ r = 1 ∨ c χ r = -1 := by
  intro M₀ y B₀ c
  have hm2 : 2 * M₀ = 2 ^ n := by
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [M₀]
    rw [hk, pow_succ, Nat.mul_div_cancel _ (by norm_num), mul_comm]
  have hM₀pos : 0 < M₀ := by
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hζ : IsPrimitiveRoot (η ^ 2) (2 * M₀) := by
    rw [hm2]
    exact hη.pow (by positivity) rfl
  have hy2m : y ^ (2 * 2 ^ n) = 1 := by
    rw [← actualRoot_orderOf n hn S e]
    exact pow_orderOf_eq_one _
  have hconj : IsConj y (y ^ (2 ^ n + 1)) := actualRoot_isConj_pow_succ n (by omega) S e
  have hexp := actual_root_signed_even_section_expansion n hn S e basis ideal principal hprincipal
    η hη
  have hcols := actual_root_principal_columns n hn S e basis ideal principal hprincipal
  have hinv : ∀ χ ∈ B₀, ∀ r < M₀, (c χ r : ℂ) = (M₀ : ℂ)⁻¹ * ∑ i ∈ Finset.range M₀,
      (η ^ 2)⁻¹ ^ (r * (2 * i + 1)) *
        (basis.representation χ).character (y ^ (2 * i + 1)) := fun χ _ r _ =>
    actualRoot_signed_even_inversion n hn S e (basis.representation χ) hη r
  have hgram : ∀ i < M₀, ∀ i' < M₀, ∑ χ ∈ B₀,
      (basis.representation χ).character (y ^ (2 * i + 1)) *
        conj ((basis.representation χ).character (y ^ (2 * i' + 1))) =
      if i = i' then (4 * M₀ : ℂ) else 0 := by
    intro i hi i' hi'
    have h := actualRoot_odd_columns_gram n hn S e basis ideal principal hprincipal hi hi'
    simpa only [Nat.cast_mul] using h
  have hcgram : ∀ r < M₀, ∀ t < M₀, ∑ χ ∈ B₀, c χ r * c χ t = if r = t then 4 else 0 :=
    fun r hr t ht => coefficient_gram_of_odd_columns B₀ hζ
      (fun χ i => (basis.representation χ).character (y ^ (2 * i + 1))) c hinv hgram hr ht
  have hcdeg : ∀ r < M₀, ∑ χ ∈ B₀, (c χ r : ℂ) * (basis.representation χ).character 1 = 0 := by
    intro r hr
    rw [Finset.sum_congr rfl fun χ hχ => by rw [hinv χ hχ r hr]]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hodd : Odd ((2 * i + 1 : ℕ) : ℤ) := ⟨i, by push_cast; ring⟩
    have h := (hcols _ hodd).2.2
    rw [zpow_natCast] at h
    calc ∑ χ ∈ B₀, (M₀ : ℂ)⁻¹ * ((η ^ 2)⁻¹ ^ (r * (2 * i + 1)) *
          (basis.representation χ).character (y ^ (2 * i + 1))) *
            (basis.representation χ).character 1
        = (M₀ : ℂ)⁻¹ * (η ^ 2)⁻¹ ^ (r * (2 * i + 1)) * ∑ χ ∈ B₀,
          (basis.representation χ).character (y ^ (2 * i + 1)) *
            (basis.representation χ).character 1 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun χ _ => ?_
          ring
      _ = 0 := by rw [h, mul_zero]
  have hprow : ∀ r < M₀, c principal r = if r = 0 then 1 else 0 := by
    have h := signed_even_coefficients_of_constant_odd_powers (basis.representation principal) y
      (2 ^ n) (by positivity) ((Nat.even_pow' (by omega)).mpr even_two) hy2m η hη hconj 1
      (fun h _ => by rw [hprincipal]; simp)
    intro r hr
    exact h r hr
  have hdegpos : ∀ χ ∈ B₀, 0 < (Module.finrank ℂ (basis.representation χ).vector : ℤ) := by
    intro χ _
    have h := irreducible_character_degree_ne_zero (basis.representation χ) (basis.irreducible χ)
    rw [FiniteComplexRepresentation.character, Representation.char_one] at h
    have h' : Module.finrank ℂ (basis.representation χ).vector ≠ 0 := by exact_mod_cast h
    omega
  have hfour : ∀ r < M₀, (B₀.filter (fun χ => c χ r ≠ 0)).card = 4 ∧
      ∀ χ ∈ B₀, c χ r = 0 ∨ c χ r = 1 ∨ c χ r = -1 := by
    intro r hr
    refine four_units_of_sq_sum_four B₀ (fun χ => c χ r)
      (fun χ => (Module.finrank ℂ (basis.representation χ).vector : ℤ)) hdegpos ?_ ?_
    · have h := hcgram r hr r hr
      rw [ite_eq_left rfl] at h
      exact h
    · have h := hcdeg r hr
      apply Int.cast_injective (α := ℂ)
      push_cast
      rw [← h]
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [FiniteComplexRepresentation.character, Representation.char_one]
  refine ⟨?_, hcgram, hcdeg, by rw [hprow 0 hM₀pos, ite_eq_left rfl], fun r hr0 hr =>
    by rw [hprow r hr, ite_eq_right (by omega)], hfour⟩
  intro χ hχ h hh z hz hzodd
  have h1 := hexp χ hχ h z hh hzodd hz
  have h2 := hexp χ hχ h 1 hh (by rw [orderOf_one]; exact odd_one) (Subgroup.one_mem _)
  rw [mul_one] at h2
  exact ⟨h1.trans h2.symm, h2⟩

end CFSG.Wreathed.ConditionalSquareRoot
