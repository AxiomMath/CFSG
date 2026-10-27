module

public import CFSG.CharacterTheory.Wreathed.FourPointGaussianColumnsDichotomy

public noncomputable section

namespace CFSG.Wreathed.FourPointGaussianColumns

open CFSG.TwoRankLowerBound.Helpers

open scoped BigOperators Classical

theorem gram_column_sums {ι : Type*} (B : Finset ι) (V : ι → Fin 2 → ℂ) (dd : ι → ℂ)
    (hgram : ∀ j k, ∑ χ ∈ B, starRingEnd ℂ (V χ j) * V χ k =
      (((!![16, 8; 8, 12] : Matrix (Fin 2) (Fin 2) ℤ) j k : ℤ) : ℂ))
    (hdeg : ∀ j, ∑ χ ∈ B, V χ j * starRingEnd ℂ (dd χ) = 0)
    (hdd : ∀ χ ∈ B, starRingEnd ℂ (dd χ) = dd χ) :
    ∑ χ ∈ B, starRingEnd ℂ (V χ 0 + 2 * V χ 1) * (V χ 0 + 2 * V χ 1) = 96 ∧
    ∑ χ ∈ B, starRingEnd ℂ (V χ 0 - V χ 1) * (V χ 0 - V χ 1) = 12 ∧
    ∑ χ ∈ B, (V χ 0 + 2 * V χ 1) * starRingEnd ℂ (V χ 0 - V χ 1) = 0 ∧
    ∑ χ ∈ B, dd χ * (V χ 0 + 2 * V χ 1) = 0 ∧ ∑ χ ∈ B, dd χ * (V χ 0 - V χ 1) = 0 := by
  have g00 := hgram 0 0
  have g01 := hgram 0 1
  have g10 := hgram 1 0
  have g11 := hgram 1 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val', Int.cast_ofNat] at g00 g01 g10 g11
  have d0 := hdeg 0
  have d1 := hdeg 1
  rw [Finset.sum_congr rfl fun χ hχ => by rw [hdd χ hχ]] at d0 d1
  have hsplit : ∀ (f₁ f₂ f₃ f₄ : ι → ℂ) (c₁ c₂ c₃ c₄ : ℂ),
      ∑ χ ∈ B, (c₁ * f₁ χ + c₂ * f₂ χ + c₃ * f₃ χ + c₄ * f₄ χ) =
        c₁ * ∑ χ ∈ B, f₁ χ + c₂ * ∑ χ ∈ B, f₂ χ + c₃ * ∑ χ ∈ B, f₃ χ +
          c₄ * ∑ χ ∈ B, f₄ χ := by
    intro f₁ f₂ f₃ f₄ c₁ c₂ c₃ c₄
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.sum_congr rfl fun χ _ => show starRingEnd ℂ (V χ 0 + 2 * V χ 1) *
        (V χ 0 + 2 * V χ 1) = 1 * (starRingEnd ℂ (V χ 0) * V χ 0) +
          2 * (starRingEnd ℂ (V χ 0) * V χ 1) + 2 * (starRingEnd ℂ (V χ 1) * V χ 0) +
          4 * (starRingEnd ℂ (V χ 1) * V χ 1) by
        simp only [map_add, map_mul, map_ofNat]
        ring, hsplit, g00, g01, g10, g11]
    norm_num
  · rw [Finset.sum_congr rfl fun χ _ => show starRingEnd ℂ (V χ 0 - V χ 1) *
        (V χ 0 - V χ 1) = 1 * (starRingEnd ℂ (V χ 0) * V χ 0) +
          (-1) * (starRingEnd ℂ (V χ 0) * V χ 1) + (-1) * (starRingEnd ℂ (V χ 1) * V χ 0) +
          1 * (starRingEnd ℂ (V χ 1) * V χ 1) by
        simp only [map_sub]
        ring, hsplit, g00, g01, g10, g11]
    norm_num
  · rw [Finset.sum_congr rfl fun χ _ => show (V χ 0 + 2 * V χ 1) *
        starRingEnd ℂ (V χ 0 - V χ 1) = 1 * (starRingEnd ℂ (V χ 0) * V χ 0) +
          (-1) * (starRingEnd ℂ (V χ 1) * V χ 0) + 2 * (starRingEnd ℂ (V χ 0) * V χ 1) +
          (-2) * (starRingEnd ℂ (V χ 1) * V χ 1) by
        simp only [map_sub]
        ring, hsplit, g00, g01, g10, g11]
    norm_num
  · have h : ∑ χ ∈ B, dd χ * (V χ 0 + 2 * V χ 1) =
        ∑ χ ∈ B, V χ 0 * dd χ + 2 * ∑ χ ∈ B, V χ 1 * dd χ := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun χ _ => by ring
    rw [h, d0, d1]
    ring
  · have h : ∑ χ ∈ B, dd χ * (V χ 0 - V χ 1) =
        ∑ χ ∈ B, V χ 0 * dd χ - ∑ χ ∈ B, V χ 1 * dd χ := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun χ _ => by ring
    rw [h, d0, d1]
    ring

theorem imag_column_sums {ι : Type*} (B : Finset ι) (T U : ι → ℂ) {i : ℂ} (hi : i ^ 2 = -1)
    (hTT : ∑ χ ∈ B, Complex.normSq (T χ) = 96) (hUU : ∑ χ ∈ B, Complex.normSq (U χ) = 12)
    (hT2 : ∑ χ ∈ B, T χ ^ 2 = 0) (hU2 : ∑ χ ∈ B, U χ ^ 2 = 0)
    (hTU : ∑ χ ∈ B, T χ * U χ = 0) (hTcU : ∑ χ ∈ B, T χ * starRingEnd ℂ (U χ) = 0) :
    ∑ χ ∈ B, imCoeff i (T χ) ^ 2 = 48 ∧ ∑ χ ∈ B, imCoeff i (U χ) ^ 2 = 6 ∧
      ∑ χ ∈ B, imCoeff i (T χ) * imCoeff i (U χ) = 0 := by
  have hre : ∀ f : ι → ℂ, ∑ χ ∈ B, f χ = 0 → ∑ χ ∈ B, (f χ).re = 0 := fun f hf => by
    rw [← Complex.re_sum, hf, Complex.zero_re]
  have key : ∀ f : ι → ℂ, ∑ χ ∈ B, (2 * imCoeff i (f χ) ^ 2) =
      ∑ χ ∈ B, Complex.normSq (f χ) - ∑ χ ∈ B, (f χ ^ 2).re := by
    intro f
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun χ _ => (normSq_sub_sq_re hi (f χ)).symm
  refine ⟨?_, ?_, ?_⟩
  · have h := key T
    rw [hTT, hre _ hT2, ← Finset.mul_sum] at h
    linarith
  · have h := key U
    rw [hUU, hre _ hU2, ← Finset.mul_sum] at h
    linarith
  · have h : ∑ χ ∈ B, (2 * imCoeff i (T χ) * imCoeff i (U χ)) =
        ∑ χ ∈ B, (T χ * starRingEnd ℂ (U χ)).re - ∑ χ ∈ B, (T χ * U χ).re := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun χ _ => (mul_conj_re_sub_mul_re hi (T χ) (U χ)).symm
    rw [hre _ hTcU, hre _ hTU, sub_zero] at h
    have h2 : ∑ χ ∈ B, (2 * imCoeff i (T χ) * imCoeff i (U χ)) =
        2 * ∑ χ ∈ B, imCoeff i (T χ) * imCoeff i (U χ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun χ _ => by ring
    linarith

theorem section_square_sums {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (a z : G) (ha : orderOf a ∣ 2 ^ 2) (hz : Odd (orderOf z)) (hcomm : Commute a z)
    (hnc : ¬ IsConj a a⁻¹) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation χ).character a ^ 2 = 0 ∧
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation χ).character (a * z) ^ 2 = 0 ∧
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation χ).character a *
          (basis.representation χ).character (a * z) = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hainv : orderOf a⁻¹ ∣ 2 ^ 2 := by rwa [orderOf_inv]
  have h1 : Nat.Coprime 2 (orderOf (1 : G)) := by rw [orderOf_one]; norm_num
  have hzc : Nat.Coprime 2 (orderOf z) := Nat.coprime_two_left.mpr hz
  have hzc' : Nat.Coprime 2 (orderOf z⁻¹) := by rwa [orderOf_inv]
  have hza : z * a = a * z := hcomm.eq.symm
  refine ⟨?_, ?_, ?_⟩
  · have h := coefficientBlock_section_column_orthogonality basis ideal 2 principal a a⁻¹ 1 1
      2 2 ha hainv h1 h1 (Commute.one_right a) (Commute.one_right a⁻¹) hnc
    simp only [mul_one, inv_inv] at h
    rw [← h]
    exact Finset.sum_congr rfl fun χ _ => sq _
  · have h := coefficientBlock_section_column_orthogonality basis ideal 2 principal a a⁻¹ z z⁻¹
      2 2 ha hainv hzc hzc' hcomm hcomm.inv_inv hnc
    rw [← h]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [← mul_inv_rev, inv_inv, hza, sq]
  · have h := coefficientBlock_section_column_orthogonality basis ideal 2 principal a a⁻¹ 1 z⁻¹
      2 2 ha hainv h1 hzc' (Commute.one_right a) hcomm.inv_inv hnc
    rw [← h]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [mul_one, ← mul_inv_rev, inv_inv, hza]

section Pairs

variable {G : Type} [Group G] [Fintype G]

@[expose] def InConjPair (χ ψ : G → ℂ) : Prop := χ = ψ ∨ χ = fun g => starRingEnd ℂ (ψ g)

@[expose] def IsDetectedPair (basis : FiniteIrreducibleCharacterBasis G) (B : Finset basis.index)
    (χ : basis.index) : Prop :=
  χ ∈ B ∧ ∀ χ' : basis.index, (∀ g, (basis.representation χ').character g =
      starRingEnd ℂ ((basis.representation χ).character g)) →
    χ' ∈ B ∧ χ' ≠ χ ∧ (basis.representation χ).character ≠ 1 ∧
      (basis.representation χ').character ≠ 1 ∧
      MonoidHom.ker (basis.representation χ).representation = ⊥ ∧
      MonoidHom.ker (basis.representation χ').representation = ⊥ ∧
      (basis.representation χ').character 1 = (basis.representation χ).character 1

@[expose] def GaussianPairDichotomy (basis : FiniteIrreducibleCharacterBasis G)
    (B : Finset basis.index) (i : ℂ) (T U : basis.index → ℂ) : Prop :=
  ∃ χ₁ ∈ B, ∃ χ₂ ∈ B, ∃ χ₃ ∈ B, χ₁ ≠ χ₂ ∧ χ₁ ≠ χ₃ ∧ χ₂ ≠ χ₃ ∧
    imCoeff i (U χ₁) = 1 ∧ imCoeff i (U χ₂) = 1 ∧ imCoeff i (U χ₃) = 1 ∧
    (∀ χ ∈ B, imCoeff i (U χ) = 1 ↔ χ = χ₁ ∨ χ = χ₂ ∨ χ = χ₃) ∧
    (∀ χ ∈ B, imCoeff i (U χ) ≠ 0 →
      InConjPair (basis.representation χ).character (basis.representation χ₁).character ∨
      InConjPair (basis.representation χ).character (basis.representation χ₂).character ∨
      InConjPair (basis.representation χ).character (basis.representation χ₃).character) ∧
    IsDetectedPair basis B χ₁ ∧ IsDetectedPair basis B χ₂ ∧ IsDetectedPair basis B χ₃ ∧
    ((imCoeff i (T χ₁) = -2 ∧ imCoeff i (T χ₂) = 1 ∧ imCoeff i (T χ₃) = 1 ∧
      ∃ ψ₁ ∈ B, ∃ ψ₂ ∈ B,
        ¬ InConjPair (basis.representation ψ₁).character (basis.representation ψ₂).character ∧
        imCoeff i (T ψ₁) = 3 ∧ imCoeff i (T ψ₂) = 3 ∧ imCoeff i (U ψ₁) = 0 ∧
        imCoeff i (U ψ₂) = 0 ∧ IsDetectedPair basis B ψ₁ ∧ IsDetectedPair basis B ψ₂ ∧
        ∀ χ ∈ B, imCoeff i (T χ) ≠ 0 →
          InConjPair (basis.representation χ).character (basis.representation χ₁).character ∨
          InConjPair (basis.representation χ).character (basis.representation χ₂).character ∨
          InConjPair (basis.representation χ).character (basis.representation χ₃).character ∨
          InConjPair (basis.representation χ).character (basis.representation ψ₁).character ∨
          InConjPair (basis.representation χ).character (basis.representation ψ₂).character) ∨
     (imCoeff i (T χ₁) = 4 ∧ imCoeff i (T χ₂) = -2 ∧ imCoeff i (T χ₃) = -2 ∧
      ∀ χ ∈ B, imCoeff i (T χ) ≠ 0 →
        InConjPair (basis.representation χ).character (basis.representation χ₁).character ∨
        InConjPair (basis.representation χ).character (basis.representation χ₂).character ∨
        InConjPair (basis.representation χ).character (basis.representation χ₃).character))

variable (basis : FiniteIrreducibleCharacterBasis G)

theorem inConjPair_of_eq {χ ψ : basis.index} (h : χ = ψ ∨ χ = conjLabel basis ψ) :
    InConjPair (basis.representation χ).character (basis.representation ψ).character := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (funext fun g => conjLabel_spec basis ψ g)

theorem isDetectedPair_of_imCoeff_ne_zero [IsSimpleGroup G]
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (i : ℂ) (χ : basis.index)
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) (g₀ : G)
    (h : imCoeff i ((basis.representation χ).character g₀) ≠ 0) :
    IsDetectedPair basis (coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
      χ := by
  refine ⟨hχ, fun χ' hχ' => ?_⟩
  have hσ : conjLabel basis χ = χ' := conjLabel_eq_of_spec basis χ χ' hχ'
  have hne1 : (basis.representation χ).character ≠ 1 := by
    intro h1
    rw [h1, Pi.one_apply, imCoeff_one] at h
    exact h rfl
  have hne1' : (basis.representation χ').character ≠ 1 := by
    intro h1
    apply hne1
    funext g
    have := hχ' g
    rw [h1, Pi.one_apply] at this
    rw [Pi.one_apply, ← Complex.conj_conj ((basis.representation χ).character g), ← this,
      map_one]
  refine ⟨hσ ▸ conjLabel_mem_coefficientBlock basis _ principal hprincipal χ hχ, ?_, hne1, hne1',
    ker_eq_bot_of_character_ne_one _ (basis.irreducible χ) hne1,
    ker_eq_bot_of_character_ne_one _ (basis.irreducible χ') hne1', ?_⟩
  · rintro rfl
    have h' := congrArg (imCoeff i) (hχ' g₀)
    rw [imCoeff_conj] at h'
    exact h (by linarith)
  · rw [hχ' 1, conj_character_one]

theorem gaussianPairDichotomy_of_sums [IsSimpleGroup G] (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {i : ℂ} (hi : i ^ 2 = -1)
    (g h : G)
    (hTint : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∃ s k : ℤ, (basis.representation χ).character g = s + k * i)
    (hUint : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∃ s k : ℤ, (basis.representation χ).character h = s + k * i)
    (hmod : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∃ s k : ℤ, (basis.representation χ).character g - (basis.representation χ).character h =
        3 * (s + k * i))
    (hTT : ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      imCoeff i ((basis.representation χ).character g) ^ 2 = 48)
    (hUU : ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      imCoeff i ((basis.representation χ).character h) ^ 2 = 6)
    (hTU : ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      imCoeff i ((basis.representation χ).character g) *
        imCoeff i ((basis.representation χ).character h) = 0) :
    GaussianPairDichotomy basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
      principal) i (fun χ => (basis.representation χ).character g)
      (fun χ => (basis.representation χ).character h) := by
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hBdef
  have hσB : ∀ χ ∈ B, conjLabel basis χ ∈ B :=
    conjLabel_mem_coefficientBlock basis _ principal hprincipal
  have hcoord : ∀ t : ℂ, (∃ s k : ℤ, t = s + k * i) → (⌊imCoeff i t⌋ : ℝ) = imCoeff i t := by
    rintro t ⟨s, k, rfl⟩
    have h1 : ((s : ℂ) + (k : ℂ) * i) = ((s : ℝ) : ℂ) + ((k : ℝ) : ℂ) * i := by push_cast; ring
    rw [h1, imCoeff_add_mul hi, Int.floor_intCast]
  set kT : basis.index → ℤ := fun χ => ⌊imCoeff i ((basis.representation χ).character g)⌋
  set kU : basis.index → ℤ := fun χ => ⌊imCoeff i ((basis.representation χ).character h)⌋
  have hkT : ∀ χ ∈ B, (kT χ : ℝ) = imCoeff i ((basis.representation χ).character g) :=
    fun χ hχ => hcoord _ (hTint χ hχ)
  have hkU : ∀ χ ∈ B, (kU χ : ℝ) = imCoeff i ((basis.representation χ).character h) :=
    fun χ hχ => hcoord _ (hUint χ hχ)
  have hsign : ∀ (k : basis.index → ℤ) (x : G),
      (∀ χ ∈ B, (k χ : ℝ) = imCoeff i ((basis.representation χ).character x)) →
      ∀ χ ∈ B, k (conjLabel basis χ) = -k χ := by
    intro k x hk χ hχ
    have h1 := hk _ (hσB χ hχ)
    rw [conjLabel_spec, imCoeff_conj, ← hk χ hχ] at h1
    exact_mod_cast h1
  have hTσ := hsign kT g hkT
  have hUσ := hsign kU h hkU
  have hUU' : ∑ χ ∈ B, kU χ ^ 2 = 6 := by
    have h1 : ∑ χ ∈ B, (kU χ : ℝ) ^ 2 = 6 := by
      rw [Finset.sum_congr rfl fun χ hχ => by rw [hkU χ hχ]]
      exact hUU
    exact_mod_cast h1
  have hTT' : ∑ χ ∈ B, kT χ ^ 2 = 48 := by
    have h1 : ∑ χ ∈ B, (kT χ : ℝ) ^ 2 = 48 := by
      rw [Finset.sum_congr rfl fun χ hχ => by rw [hkT χ hχ]]
      exact hTT
    exact_mod_cast h1
  have hTU' : ∑ χ ∈ B, kT χ * kU χ = 0 := by
    have h1 : ∑ χ ∈ B, (kT χ : ℝ) * (kU χ : ℝ) = 0 := by
      rw [Finset.sum_congr rfl fun χ hχ => by rw [hkT χ hχ, hkU χ hχ]]
      exact hTU
    exact_mod_cast h1
  have hmod' : ∀ χ ∈ B, 3 ∣ kT χ - kU χ := by
    intro χ hχ
    obtain ⟨s, k, hsk⟩ := hmod χ hχ
    refine ⟨k, ?_⟩
    have h1 : imCoeff i ((basis.representation χ).character g -
        (basis.representation χ).character h) = 3 * k := by
      rw [hsk, show (3 * ((s : ℂ) + (k : ℂ) * i)) =
        (((3 * s : ℝ)) : ℂ) + ((3 * k : ℝ) : ℂ) * i by push_cast; ring, imCoeff_add_mul hi]
    rw [imCoeff_sub, ← hkT χ hχ, ← hkU χ hχ] at h1
    exact_mod_cast h1
  obtain ⟨χ₁, χ₂, χ₃, h1B, h2B, h3B, h12, h13, h23, hU1, hU2, hU3, hU1iff, hUpairs, hcase⟩ :=
    conjugate_pair_dichotomy B (conjLabel basis) hσB (conjLabel_conjLabel basis) kT kU hTσ hUσ
      hUU' hTT' hTU' hmod'
  have hval : ∀ (k : basis.index → ℤ) (x : G),
      (∀ χ ∈ B, (k χ : ℝ) = imCoeff i ((basis.representation χ).character x)) →
      ∀ χ ∈ B, ∀ c : ℤ, k χ = c → imCoeff i ((basis.representation χ).character x) = c := by
    intro k x hk χ hχ c hc
    rw [← hk χ hχ, hc]
  have hne : ∀ (k : basis.index → ℤ) (x : G),
      (∀ χ ∈ B, (k χ : ℝ) = imCoeff i ((basis.representation χ).character x)) →
      ∀ χ ∈ B, imCoeff i ((basis.representation χ).character x) ≠ 0 → k χ ≠ 0 := by
    intro k x hk χ hχ hne hk0
    rw [← hk χ hχ, hk0, Int.cast_zero] at hne
    exact hne rfl
  have hdet : ∀ χ ∈ B, ∀ c : ℤ, c ≠ 0 → ∀ x : G,
      imCoeff i ((basis.representation χ).character x) = c → IsDetectedPair basis B χ :=
    fun χ hχ c hc x hx => isDetectedPair_of_imCoeff_ne_zero basis ideal principal hprincipal i
      χ hχ x (by rw [hx]; exact_mod_cast hc)
  have hU1' := hval kU h hkU χ₁ h1B 1 hU1
  have hU2' := hval kU h hkU χ₂ h2B 1 hU2
  have hU3' := hval kU h hkU χ₃ h3B 1 hU3
  push_cast at hU1' hU2' hU3'
  have hpair3 : ∀ χ, (χ = χ₁ ∨ χ = conjLabel basis χ₁ ∨ χ = χ₂ ∨ χ = conjLabel basis χ₂ ∨
      χ = χ₃ ∨ χ = conjLabel basis χ₃) →
      InConjPair (basis.representation χ).character (basis.representation χ₁).character ∨
      InConjPair (basis.representation χ).character (basis.representation χ₂).character ∨
      InConjPair (basis.representation χ).character (basis.representation χ₃).character := by
    intro χ hχ
    rcases hχ with h' | h' | h' | h' | h' | h'
    · exact Or.inl (inConjPair_of_eq basis (Or.inl h'))
    · exact Or.inl (inConjPair_of_eq basis (Or.inr h'))
    · exact Or.inr (Or.inl (inConjPair_of_eq basis (Or.inl h')))
    · exact Or.inr (Or.inl (inConjPair_of_eq basis (Or.inr h')))
    · exact Or.inr (Or.inr (inConjPair_of_eq basis (Or.inl h')))
    · exact Or.inr (Or.inr (inConjPair_of_eq basis (Or.inr h')))
  refine ⟨χ₁, h1B, χ₂, h2B, χ₃, h3B, h12, h13, h23, hU1', hU2', hU3', fun χ hχ => ?_,
    fun χ hχ hne' => hpair3 χ (hUpairs χ hχ (hne kU h hkU χ hχ hne')),
    hdet χ₁ h1B 1 one_ne_zero h (by rw [hU1']; norm_num),
    hdet χ₂ h2B 1 one_ne_zero h (by rw [hU2']; norm_num),
    hdet χ₃ h3B 1 one_ne_zero h (by rw [hU3']; norm_num), ?_⟩
  · rw [← hU1iff χ hχ, ← hkU χ hχ]
    exact_mod_cast Iff.rfl
  rcases hcase with ⟨e1, e2, e3, ψ₁, hψ₁, ψ₂, hψ₂, hψ12, hψσ, hT1, hT2, hU1ψ, hU2ψ, hrest⟩ |
    ⟨e1, e2, e3, hrest⟩
  · left
    have e1' := hval kT g hkT χ₁ h1B _ e1
    have e2' := hval kT g hkT χ₂ h2B _ e2
    have e3' := hval kT g hkT χ₃ h3B _ e3
    have hT1' := hval kT g hkT ψ₁ hψ₁ _ hT1
    have hT2' := hval kT g hkT ψ₂ hψ₂ _ hT2
    have hU1ψ' := hval kU h hkU ψ₁ hψ₁ _ hU1ψ
    have hU2ψ' := hval kU h hkU ψ₂ hψ₂ _ hU2ψ
    push_cast at e1' e2' e3' hT1' hT2' hU1ψ' hU2ψ'
    refine ⟨e1', e2', e3', ψ₁, hψ₁, ψ₂, hψ₂, ?_, hT1', hT2', hU1ψ', hU2ψ',
      hdet ψ₁ hψ₁ 3 (by norm_num) g (by rw [hT1']; norm_num),
      hdet ψ₂ hψ₂ 3 (by norm_num) g (by rw [hT2']; norm_num), fun χ hχ hne' => ?_⟩
    · rintro (h' | h')
      · exact hψ12 (basis.distinct h')
      · apply hψσ
        apply basis.distinct
        show (basis.representation ψ₁).character =
          (basis.representation (conjLabel basis ψ₂)).character
        rw [h']
        exact (funext fun x => conjLabel_spec basis ψ₂ x).symm
    · rcases hrest χ hχ (hne kT g hkT χ hχ hne') with h' | h' | h' | h' | h' | h' | h' | h' |
        h' | h'
      · exact Or.inl (inConjPair_of_eq basis (Or.inl h'))
      · exact Or.inl (inConjPair_of_eq basis (Or.inr h'))
      · exact Or.inr (Or.inl (inConjPair_of_eq basis (Or.inl h')))
      · exact Or.inr (Or.inl (inConjPair_of_eq basis (Or.inr h')))
      · exact Or.inr (Or.inr (Or.inl (inConjPair_of_eq basis (Or.inl h'))))
      · exact Or.inr (Or.inr (Or.inl (inConjPair_of_eq basis (Or.inr h'))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (inConjPair_of_eq basis (Or.inl h')))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (inConjPair_of_eq basis (Or.inr h')))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (inConjPair_of_eq basis (Or.inl h')))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (inConjPair_of_eq basis (Or.inr h')))))
  · right
    have e1' := hval kT g hkT χ₁ h1B _ e1
    have e2' := hval kT g hkT χ₂ h2B _ e2
    have e3' := hval kT g hkT χ₃ h3B _ e3
    push_cast at e1' e2' e3'
    exact ⟨e1', e2', e3', fun χ hχ hne' => hpair3 χ (hrest χ hχ (hne kT g hkT χ hχ hne'))⟩

end Pairs

end CFSG.Wreathed.FourPointGaussianColumns
