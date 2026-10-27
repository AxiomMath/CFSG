module

public import CFSG.CharacterTheory.Wreathed.ConditionalSquareRootColumns
public import CFSG.CharacterTheory.Wreathed.ConditionalFlatTwistedBasesTwist
public import CFSG.CharacterTheory.Wreathed.UniqueLocalBlockSectionColumns

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.FlatSquareRoot

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.ConditionalFourier
  CFSG.Wreathed.ConditionalSquareRoot CFSG.Wreathed.WreathCentralSquare
  CFSG.Wreathed.SquareRootSmallCharacterRigidity CFSG.Semidihedral.Principal

variable {G : Type} [Group G] [Fintype G]

theorem singleton_section_column (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (B : basis.index) {u : G} {r : ℕ}
    (hr : 1 ≤ r) (hu : orderOf u = 2 ^ r) (hgroup : IsPGroup 2 (Subgroup.zpowers u))
    (lamG : G → ℂ) (hlam1 : lamG 1 = 1)
    (hlocal : ∀ (lb : FiniteIrreducibleCharacterBasis
        (Subgroup.centralizer (Subgroup.zpowers u : Set G))) (ℓ : lb.index),
      (∀ c, (lb.representation ℓ).character c = lamG c) →
      brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers u) hgroup
          (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
          (Subgroup.centralizer_le_normalizer _) lb ℓ =
        centralCharacterResidueHom basis ideal B ∧
      ∀ θ, brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers u) hgroup
          (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
          (Subgroup.centralizer_le_normalizer _) lb θ =
        centralCharacterResidueHom basis ideal B →
        θ ∈ coefficientBlock lb (localizedComplexIntegerRing ideal) ℓ)
    (localBasis : FiniteIrreducibleCharacterBasis
      (Subgroup.centralizer (Subgroup.zpowers u : Set G))) (ℓ : localBasis.index)
    (hℓ : ∀ c, (localBasis.representation ℓ).character c = lamG c) (c : ℕ)
    (hdata : SingletonTwistedBasisData localBasis ideal ℓ (fun c => lamG c) c) :
    (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
      ∀ z ∈ Subgroup.centralizer (Subgroup.zpowers u : Set G), Odd (orderOf z) →
        (basis.representation χ).character (u * z) =
          lamG z * (basis.representation χ).character u) ∧
    (∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
      (basis.representation χ).character u * conj ((basis.representation χ).character u) = c) ∧
    ∀ g : G, (∀ a c : G, a * c = g → Commute a c → (∃ e : ℕ, orderOf a = 2 ^ e) →
        Odd (orderOf c) → ¬ IsConj a u) →
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        (basis.representation χ).character u * conj ((basis.representation χ).character g) = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd_iff : ∀ n : ℕ, ¬ 2 ∣ n ↔ Odd n := fun n => by
    rw [Nat.odd_iff, Nat.two_dvd_ne_zero]
  obtain ⟨hbrauer, hunique⟩ := hlocal localBasis ℓ hℓ
  let b : Fin 1 → Subgroup.centralizer (Subgroup.zpowers u : Set G) → ℂ := ![fun c => lamG c]
  have hb0 : ∀ y, b 0 y = lamG y := fun y => rfl
  have hℓmem := coefficientBlock_self_mem localBasis (localizedComplexIntegerRing ideal) ℓ
  have hbmem : ∀ j, ∃ c : localBasis.index → ℂ, ∀ y, ¬ 2 ∣ orderOf y →
      b j y = ∑ θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) ℓ,
        c θ * (localBasis.representation θ).character y := by
    intro j
    refine ⟨fun θ => if θ = ℓ then 1 else 0, fun y _ => ?_⟩
    rw [Subsingleton.elim j 0, hb0]
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' _ ℓ, ite_eq_left hℓmem, hℓ]
  have hbindep : ∀ c : Fin 1 → ℂ, (∀ y, ¬ 2 ∣ orderOf y → ∑ j, c j * b j y = 0) → c = 0 := by
    intro c hc
    have h := hc 1 (by rw [orderOf_one]; norm_num)
    rw [Fin.sum_univ_one, hb0] at h
    simp only [OneMemClass.coe_one, hlam1, mul_one] at h
    funext j
    rw [Subsingleton.elim j 0, h]
    rfl
  let d : localBasis.index → Fin 1 → ℤ := fun _ _ => 1
  have hd : ∀ θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) ℓ,
      ∀ y, ¬ 2 ∣ orderOf y →
        (localBasis.representation θ).character y = ∑ j, (d θ j : ℂ) * b j y := by
    intro θ hθ y hy
    have h := congrFun (hdata.restriction θ hθ) ⟨y, (hodd_iff _).mp hy⟩
    rw [Fin.sum_univ_one, hb0]
    simp only [oddRestriction] at h
    rw [h]
    simp [d]
  obtain ⟨U, -, -, -, -, -, -, hrow, -, hUgram, hvanish⟩ :=
    unique_local_block_primary_section_integral_columns basis ideal 2 hr hu hgroup localBasis B
      ℓ hbrauer hunique (Complex.isPrimitiveRoot_exp (2 ^ r) (pow_ne_zero _ two_ne_zero)) 1
      le_rfl b hbmem hbindep d hd
  have hU : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
      U χ 0 = (basis.representation χ).character u := by
    intro χ hχ
    have h := hrow χ hχ 1 (by rw [orderOf_one]; norm_num)
    rw [Fin.sum_univ_one, hb0] at h
    simp only [OneMemClass.coe_one, hlam1, mul_one] at h
    exact h.symm
  refine ⟨fun χ hχ z hz hzodd => ?_, ?_, fun g hg => ?_⟩
  · have h := hrow χ hχ ⟨z, hz⟩ ((hodd_iff _).mpr (by rwa [Subgroup.orderOf_mk]))
    rw [Fin.sum_univ_one, hb0, hU χ hχ] at h
    rw [show u * z = u * ((⟨z, hz⟩ : Subgroup.centralizer (Subgroup.zpowers u : Set G)) : G)
      from rfl, h]
    ring
  · have h := hUgram 0 0
    simp only [d, mul_one, Int.cast_one, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    rw [hdata.card] at h
    rw [← h]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [hU χ hχ, mul_comm]
  · have h := hvanish g (fun a c hac hcomm ha hc => hg a c hac hcomm ha ((hodd_iff _).mp hc)) 0
    rw [← h]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [hU χ hχ]

theorem flat_signed_even_columns (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (B : basis.index)
    (lamG : G → ℂ) {θ : ℂ} (hθ : IsPrimitiveRoot θ (2 * 2 ^ n))
    (hsec : ∀ h : ℤ, Odd h →
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        ∀ z ∈ Subgroup.centralizer ({actualRoot S e} : Set G), Odd (orderOf z) →
          (basis.representation χ).character (actualRoot S e ^ h * z) =
            lamG z * (basis.representation χ).character (actualRoot S e ^ h)) ∧
      (∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        (basis.representation χ).character (actualRoot S e ^ h) *
          conj ((basis.representation χ).character (actualRoot S e ^ h)) = 2 * 2 ^ n) ∧
      ∀ g : G, (∀ a c : G, a * c = g → Commute a c → (∃ e : ℕ, orderOf a = 2 ^ e) →
          Odd (orderOf c) → ¬ IsConj a (actualRoot S e ^ h)) →
        ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
          (basis.representation χ).character (actualRoot S e ^ h) *
            conj ((basis.representation χ).character g) = 0) :
    let M₀ := 2 ^ n / 2
    let y := actualRoot S e
    let BB := coefficientBlock basis (localizedComplexIntegerRing ideal) B
    let c : basis.index → ℕ → ℤ := fun χ r =>
      signedEvenEigenmultiplicity (basis.representation χ) y θ (2 ^ n) r
    (∀ χ ∈ BB, ∀ h : ℤ, Odd h → ∀ z ∈ Subgroup.centralizer ({y} : Set G), Odd (orderOf z) →
      (basis.representation χ).character (y ^ h * z) =
          lamG z * (basis.representation χ).character (y ^ h) ∧
      (basis.representation χ).character (y ^ h) =
        ∑ r ∈ Finset.range M₀, (c χ r : ℂ) * (θ ^ 2) ^ ((r : ℤ) * h)) ∧
    (∀ r < M₀, ∀ t < M₀, ∑ χ ∈ BB, c χ r * c χ t = if r = t then 4 else 0) ∧
    (∀ r < M₀, ∀ z : G, Odd (orderOf z) →
      ∑ χ ∈ BB, (c χ r : ℂ) * conj ((basis.representation χ).character z) = 0) ∧
    ∀ r < M₀, (BB.filter (fun χ => c χ r ≠ 0)).card = 4 ∧
      ∀ χ ∈ BB, c χ r = 0 ∨ c χ r = 1 ∨ c χ r = -1 := by
  intro M₀ y BB c
  have hm2 : 2 * M₀ = 2 ^ n := by
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [M₀]
    rw [hk, pow_succ, Nat.mul_div_cancel _ (by norm_num), mul_comm]
  have hM₀pos : 0 < M₀ := by
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hζ : IsPrimitiveRoot (θ ^ 2) (2 * M₀) := by
    rw [hm2]
    exact hθ.pow (by positivity) rfl
  have hy2m : y ^ (2 * 2 ^ n) = 1 := by
    rw [← actualRoot_orderOf n hn S e]
    exact pow_orderOf_eq_one _
  have hconj : IsConj y (y ^ (2 ^ n + 1)) := actualRoot_isConj_pow_succ n (by omega) S e
  have hy2 : orderOf y = 2 ^ (n + 1) := by rw [actualRoot_orderOf n hn S e, pow_succ, mul_comm]
  have hodd : ∀ j : ℕ, Odd ((2 * j + 1 : ℕ) : ℤ) := fun j => ⟨j, by push_cast; ring⟩
  have hz : ∀ j : ℕ, y ^ (2 * j + 1) = y ^ ((2 * j + 1 : ℕ) : ℤ) :=
    fun j => (zpow_natCast _ _).symm
  have hne1 : ∀ h : ℤ, Odd h → y ^ h ≠ 1 := by
    intro h hh h1
    have hord := orderOf_odd_power hy2 hh
    rw [h1, orderOf_one] at hord
    exact (Nat.one_lt_two_pow (by omega)).ne' hord.symm
  have hgram : ∀ i < M₀, ∀ i' < M₀, ∑ χ ∈ BB,
      (basis.representation χ).character (y ^ (2 * i + 1)) *
        conj ((basis.representation χ).character (y ^ (2 * i' + 1))) =
      if i = i' then (4 * M₀ : ℂ) else 0 := by
    intro i hi i' hi'
    split_ifs with hii
    · subst hii
      rw [hz]
      rw [(hsec _ (hodd i)).2.1]
      have hnum : (2 * 2 ^ n : ℕ) = 4 * M₀ := by omega
      exact_mod_cast hnum
    · rw [hz, hz]
      refine (hsec _ (hodd i)).2.2 _ fun a' c' hac hcomm ha hc hconj' => ?_
      have heq : a' = y ^ ((2 * i' + 1 : ℕ) : ℤ) :=
        two_part_eq_self ⟨n + 1, orderOf_odd_power hy2 (hodd i')⟩ hac hcomm ha
          (fun h2 => (Nat.not_even_iff_odd.mpr hc) (even_iff_two_dvd.mpr h2))
      rw [heq] at hconj'
      have hmod := (actualRoot_odd_zpow_isConj_iff n hn S e (hodd i') (hodd i)).mp hconj'
      have hmod' : (2 * i' + 1) % 2 ^ n = (2 * i + 1) % 2 ^ n := by
        have h1 : (((2 * i' + 1) % 2 ^ n : ℕ) : ℤ) = (((2 * i + 1) % 2 ^ n : ℕ) : ℤ) := by
          rw [Int.natCast_mod, Int.natCast_mod]
          exact hmod
        exact_mod_cast h1
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod'
      exact hii (by omega)
  have hinv : ∀ χ ∈ BB, ∀ r < M₀, (c χ r : ℂ) = (M₀ : ℂ)⁻¹ * ∑ i ∈ Finset.range M₀,
      (θ ^ 2)⁻¹ ^ (r * (2 * i + 1)) *
        (basis.representation χ).character (y ^ (2 * i + 1)) := fun χ _ r _ =>
    actualRoot_signed_even_inversion n hn S e (basis.representation χ) hθ r
  have hcgram : ∀ r < M₀, ∀ t < M₀, ∑ χ ∈ BB, c χ r * c χ t = if r = t then 4 else 0 :=
    fun r hr t ht => coefficient_gram_of_odd_columns BB hζ
      (fun χ i => (basis.representation χ).character (y ^ (2 * i + 1))) c hinv hgram hr ht
  have hcodd : ∀ r < M₀, ∀ z : G, Odd (orderOf z) →
      ∑ χ ∈ BB, (c χ r : ℂ) * conj ((basis.representation χ).character z) = 0 := by
    intro r hr z hz'
    have hvan : ∀ i : ℕ, ∑ χ ∈ BB, (basis.representation χ).character (y ^ (2 * i + 1)) *
        conj ((basis.representation χ).character z) = 0 := by
      intro i
      rw [hz]
      refine (hsec _ (hodd i)).2.2 z fun a' c' hac hcomm ha hc hconj' => ?_
      have heq := two_part_unique (show (1 : G) * z = z from one_mul z) (Commute.one_left z)
        ⟨0, by rw [orderOf_one, pow_zero]⟩ hz' hac hcomm ha hc
      rw [← heq] at hconj'
      exact hne1 _ (hodd i) (isConj_one_right.mp hconj')
    rw [Finset.sum_congr rfl fun χ hχ => by rw [hinv χ hχ r hr]]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    calc ∑ χ ∈ BB, (M₀ : ℂ)⁻¹ * ((θ ^ 2)⁻¹ ^ (r * (2 * i + 1)) *
          (basis.representation χ).character (y ^ (2 * i + 1))) *
            conj ((basis.representation χ).character z)
        = (M₀ : ℂ)⁻¹ * (θ ^ 2)⁻¹ ^ (r * (2 * i + 1)) * ∑ χ ∈ BB,
          (basis.representation χ).character (y ^ (2 * i + 1)) *
            conj ((basis.representation χ).character z) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun χ _ => ?_
          ring
      _ = 0 := by rw [hvan i, mul_zero]
  have hdegpos : ∀ χ ∈ BB, 0 < (Module.finrank ℂ (basis.representation χ).vector : ℤ) := by
    intro χ _
    have h := irreducible_character_degree_ne_zero (basis.representation χ) (basis.irreducible χ)
    rw [FiniteComplexRepresentation.character, Representation.char_one] at h
    have h' : Module.finrank ℂ (basis.representation χ).vector ≠ 0 := by exact_mod_cast h
    omega
  have hfour : ∀ r < M₀, (BB.filter (fun χ => c χ r ≠ 0)).card = 4 ∧
      ∀ χ ∈ BB, c χ r = 0 ∨ c χ r = 1 ∨ c χ r = -1 := by
    intro r hr
    refine four_units_of_sq_sum_four BB (fun χ => c χ r)
      (fun χ => (Module.finrank ℂ (basis.representation χ).vector : ℤ)) hdegpos ?_ ?_
    · have h := hcgram r hr r hr
      rw [ite_eq_left rfl] at h
      exact h
    · have h := hcodd r hr 1 (by rw [orderOf_one]; exact odd_one)
      apply Int.cast_injective (α := ℂ)
      push_cast
      rw [← h]
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [FiniteComplexRepresentation.character, Representation.char_one, Complex.conj_natCast]
  refine ⟨fun χ hχ h hh z hz' hzodd => ⟨(hsec h hh).1 χ hχ z hz' hzodd, ?_⟩, hcgram, hcodd,
    hfour⟩
  exact signed_even_character_zpow_expansion _ _ _ (pow_pos (by omega) _)
    (Even.pow_of_ne_zero even_two (by omega)) hy2m θ hθ hconj h hh

end CFSG.Wreathed.FlatSquareRoot
