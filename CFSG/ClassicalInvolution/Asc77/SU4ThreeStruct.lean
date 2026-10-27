module

public import CFSG.ClassicalInvolution.Asc77.SU4Struct

public section

namespace CFSG.ClassicalInvolution.RouteD.SU4Pattern

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Models
  CFSG.LieType.Steinberg

section Arith

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_sqrt_neg_one_three (hK : Nat.card K = (p ^ f) ^ 2) (hq3 : p ^ f % 4 = 3) :
    ∃ ι : K, ι * ι = -1 ∧ unitaryInvolution K p f ι = -ι := by
  classical
  have := Fintype.ofFinite K
  have hsq : IsSquare (-1 : K) := by
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hK, Nat.pow_mod, hq3]
    norm_num
  obtain ⟨ι, hι⟩ := hsq
  have hι' : ι * ι = -1 := hι.symm
  set σ := unitaryInvolution K p f with hσ
  refine ⟨ι, hι', ?_⟩
  have h1 : σ ι * σ ι = -1 := by rw [← map_mul, hι', map_neg, map_one]
  have h2 : (σ ι - ι) * (σ ι + ι) = 0 := by linear_combination h1 - hι'
  rcases mul_eq_zero.mp h2 with h | h
  · exfalso
    have hfix : ι ∈ fixedSubfield K p f := mem_fixedSubfield.2 (sub_eq_zero.mp h)
    have := Fintype.ofFinite (fixedSubfield K p f)
    have hsq' : IsSquare (-1 : fixedSubfield K p f) := ⟨⟨ι, hfix⟩, Subtype.ext (by
      simpa using hι'.symm)⟩
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, card_fixedSubfield hK] at hsq'
    exact hsq' hq3
  · exact eq_neg_of_add_eq_zero_left h

omit [Finite K] in
theorem eq_smul_conjTr_of_sq (σ : K ≃+* K) {n : ℕ} {G : Matrix (Fin n) (Fin n) K} {s : K}
    (hiso : conjTr σ G * G = 1) (hsq : G * G = s • (1 : Matrix (Fin n) (Fin n) K)) :
    G = s • conjTr σ G := by
  calc G = (conjTr σ G * G) * G := by rw [hiso, Matrix.one_mul]
    _ = conjTr σ G * (G * G) := by rw [Matrix.mul_assoc]
    _ = s • conjTr σ G := by rw [hsq, Matrix.mul_smul, Matrix.mul_one]

omit [Finite K] in
theorem blockMat_zero_eq_BD (X : Matrix (Fin 2) (Fin 2) K) :
    blockMat 4 0 X = BD X (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [BD_eq]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [blockMat_apply]

theorem blockDiag_of_normalizes (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {G : Matrix (Fin 4) (Fin 4) K} (hiso : conjTr (unitaryInvolution K p f) G * G = 1)
    (hsq : ∃ s : K, G * G = s • (1 : Matrix (Fin 4) (Fin 4) K))
    (hnorm : ∀ A : Su K p f 2, ∃ A' : Matrix (Fin 2) (Fin 2) K,
      G * blockMat 4 0 (suMat A) = blockMat 4 0 A' * G) :
    G = BD !![G 0 0, G 0 1; G 1 0, G 1 1] !![G 2 2, G 2 3; G 3 2, G 3 3] := by
  obtain ⟨u, hu, hne⟩ := exists_norm_one_ne hK hp2 hq
  set σ := unitaryInvolution K p f with hσ
  have hσσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hK
  have hu' : u * σ u = 1 := by rw [mul_comm]; exact hu
  have hu1 : u ≠ 1 := by
    rintro rfl
    apply hne
    simp
  have hu1' : σ u ≠ 1 := by
    intro h1
    apply hu1
    have := congrArg σ h1
    rwa [hσσ, map_one] at this
  have hdet1 : (!![u, 0; 0, σ u] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.det_fin_two_of]
    simp [hu']
  have hiso1 : conjTr σ (!![u, 0; 0, σ u] : Matrix (Fin 2) (Fin 2) K) *
      (!![u, 0; 0, σ u] : Matrix (Fin 2) (Fin 2) K) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two, hσσ, hu, hu']
  obtain ⟨s, hs⟩ := hsq
  have hGs : G = s • conjTr σ G := eq_smul_conjTr_of_sq σ hiso hs
  obtain ⟨A', hA'⟩ := hnorm (mkSU K p f _ hdet1 hiso1)
  rw [suMat_mkSU] at hA'
  have e20 := congrFun (congrFun hA' 2) 0
  have e30 := congrFun (congrFun hA' 3) 0
  have e21 := congrFun (congrFun hA' 2) 1
  have e31 := congrFun (congrFun hA' 3) 1
  simp [Matrix.mul_apply, blockMat_apply, Fin.sum_univ_four] at e20 e30 e21 e31
  have z20 : G 2 0 = 0 := by
    have : G 2 0 * (u - 1) = 0 := by linear_combination e20
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hu1)
  have z30 : G 3 0 = 0 := by
    have : G 3 0 * (u - 1) = 0 := by linear_combination e30
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hu1)
  have z21 : G 2 1 = 0 := by
    have : G 2 1 * (σ u - 1) = 0 := by linear_combination e21
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hu1')
  have z31 : G 3 1 = 0 := by
    have : G 3 1 * (σ u - 1) = 0 := by linear_combination e31
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hu1')
  have hT : ∀ i j : Fin 4, G i j = s * σ (G j i) := fun i j => by
    have := congrFun (congrFun hGs i) j
    simpa [conjTr] using this
  have z02 : G 0 2 = 0 := by rw [hT, z20, map_zero, mul_zero]
  have z03 : G 0 3 = 0 := by rw [hT, z30, map_zero, mul_zero]
  have z12 : G 1 2 = 0 := by rw [hT, z21, map_zero, mul_zero]
  have z13 : G 1 3 = 0 := by rw [hT, z31, map_zero, mul_zero]
  rw [BD_eq]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [z20, z30, z21, z31, z02, z03, z12, z13]

omit [Finite K] in
theorem conjTr_smul_aux (σ : K ≃+* K) (x : K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    conjTr σ (x • A) = σ x • conjTr σ A := by
  ext i j
  simp [conjTr]

theorem block_data_three (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hq3 : p ^ f % 4 = 3) {G : Matrix (Fin 4) (Fin 4) K}
    (hiso : conjTr (unitaryInvolution K p f) G * G = 1) (hsq : ∃ s : K, G * G = s • 1)
    (hnorm : ∀ A : Su K p f 2, ∃ A' : Matrix (Fin 2) (Fin 2) K,
      G * blockMat 4 0 (suMat A) = blockMat 4 0 A' * G)
    (hnon : ∀ r : Su K p f 2, ∃ A : Su K p f 2,
      G * blockMat 4 0 (suMat A) ≠ blockMat 4 0 (suMat r * suMat A * suMat r⁻¹) * G) :
    ∃ (a : K) (H₁ H₂ : Matrix (Fin 2) (Fin 2) K), G = BD H₁ H₂ ∧
      unitaryInvolution K p f a * a = -1 ∧
      conjTr (unitaryInvolution K p f) H₁ * H₁ = 1 ∧ H₁ * H₁ = a ^ 2 • 1 ∧ H₁ ≠ a • 1 ∧
      H₁ ≠ (-a) • 1 ∧ conjTr (unitaryInvolution K p f) H₂ * H₂ = 1 ∧ H₂ * H₂ = a ^ 2 • 1 ∧
      H₂ ≠ a • 1 ∧ H₂ ≠ (-a) • 1 := by
  classical
  set σ := unitaryInvolution K p f with hσ
  have h2 : (2 : K) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_charP_ne_two hp2
  obtain ⟨s, hs⟩ := hsq
  have hGform := blockDiag_of_normalizes hK hp2 hq hiso ⟨s, hs⟩ hnorm
  set P : Matrix (Fin 2) (Fin 2) K := !![G 0 0, G 0 1; G 1 0, G 1 1] with hP
  set T : Matrix (Fin 2) (Fin 2) K := !![G 2 2, G 2 3; G 3 2, G 3 3] with hT
  clear_value P T
  clear hP hT
  subst hGform
  rw [conjTr_BD, BD_mul, ← BD_one] at hiso
  obtain ⟨hI1, hI2⟩ := BD_inj hiso
  rw [BD_mul, ← BD_smul_one] at hs
  obtain ⟨hS1, hS2⟩ := BD_inj hs
  have hnon' : ∀ r : Su K p f 2, ∃ A : Su K p f 2,
      P * suMat A ≠ (suMat r * suMat A * suMat r⁻¹) * P := by
    intro r
    obtain ⟨A, hA⟩ := hnon r
    refine ⟨A, fun h => hA ?_⟩
    rw [blockMat_zero_eq_BD, blockMat_zero_eq_BD, BD_mul, BD_mul, Matrix.mul_one, Matrix.one_mul,
      h]
  have hPns : ∀ d : K, P ≠ d • 1 := by
    intro d hd
    obtain ⟨A, hA⟩ := hnon' 1
    apply hA
    rw [hd, suMat_one, inv_one, suMat_one, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul]
  have e00 := congrFun (congrFun hS1 0) 0
  have e01 := congrFun (congrFun hS1 0) 1
  have e10 := congrFun (congrFun hS1 1) 0
  have e11 := congrFun (congrFun hS1 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have htr : P 0 0 + P 1 1 = 0 := by
    by_contra hne
    have hb : P 0 1 = 0 := by
      have : P 0 1 * (P 0 0 + P 1 1) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right hne
    have hc : P 1 0 = 0 := by
      have : P 1 0 * (P 0 0 + P 1 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right hne
    have had : P 0 0 = P 1 1 := by
      have : (P 0 0 - P 1 1) * (P 0 0 + P 1 1) = 0 := by
        rw [hb, hc] at e00 e11
        linear_combination e00 - e11
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hne)
    apply hPns (P 0 0)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, had]
  have hdetP : P.det = -s := by
    rw [Matrix.det_fin_two]
    have : P 1 1 = -P 0 0 := by linear_combination htr
    rw [this]
    linear_combination (-1 : K) * e00
  have hdetN : σ P.det * P.det = 1 := by
    have h1 := congrArg Matrix.det hI1
    have e : (conjTr σ P).det = σ P.det := by
      show ((P.map σ)ᵀ).det = σ P.det
      rw [Matrix.det_transpose]
      exact (RingHom.map_det (σ : K →+* K) P).symm
    rw [Matrix.det_mul, e, Matrix.det_one] at h1
    exact h1
  have hev : Even (p ^ f + 1) := ⟨(p ^ f + 1) / 2, by omega⟩
  have hs1 : s ^ (p ^ f + 1) = 1 := by
    have := norm_pow_eq_one (K := K) (p := p) (f := f) hdetN
    rw [hdetP, neg_pow, hev.neg_one_pow, one_mul] at this
    exact this
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hs1
    exact zero_ne_one hs1
  obtain ⟨a, ha⟩ : ∃ a : K, a ^ 2 = s := by
    have := Fintype.ofFinite K
    have hrc : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
    have hsqr : IsSquare s := by
      rw [FiniteField.isSquare_iff hrc hs0, ← Nat.card_eq_fintype_card, hK]
      obtain ⟨m, hm⟩ : ∃ m, p ^ f = 2 * m + 1 := ⟨p ^ f / 2, by omega⟩
      have h3 : (p ^ f) ^ 2 = 2 * ((p ^ f + 1) * m) + 1 := by rw [hm]; ring
      have h4 : (p ^ f) ^ 2 / 2 = (p ^ f + 1) * m := by
        rw [h3, Nat.mul_add_div (by norm_num)]
        norm_num
      rw [h4, pow_mul, hs1, one_pow]
    obtain ⟨a, hasq⟩ := hsqr
    exact ⟨a, by rw [hasq]; ring⟩
  have hanorm : σ a * a = 1 ∨ σ a * a = -1 := by
    have h1 : a ^ (p ^ f + 1) * a ^ (p ^ f + 1) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, ha, hs1]
    have h2' : σ a * a = a ^ (p ^ f + 1) := by
      rw [hσ, unitaryInvolution_apply, ← pow_succ]
    rw [h2']
    exact mul_self_eq_one_iff.mp h1
  rcases hanorm with hn1 | hn1
  ·
    exfalso
    obtain ⟨ι, hι, hσι⟩ := exists_sqrt_neg_one_three hK hq3
    set e : K := a * ι with he
    have hσe : σ e * e = 1 := by
      rw [he, map_mul, hσι]
      linear_combination (-(ι * ι)) * hn1 - hι
    have he2 : e * e = -s := by
      have : a * ι * (a * ι) = a ^ 2 * (ι * ι) := by ring
      rw [he, this, hι, ha]
      ring
    have he0 : e ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at he2
      exact hs0 (neg_eq_zero.mp he2.symm)
    have hriso : conjTr σ (e⁻¹ • P) * (e⁻¹ • P) = 1 := by
      have : σ e⁻¹ * e⁻¹ = 1 := by rw [map_inv₀, ← mul_inv, hσe, inv_one]
      rw [conjTr_smul_aux, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hI1, this, one_smul]
    have hrdet : (e⁻¹ • P).det = 1 := by
      rw [Matrix.det_smul, hdetP]
      simp only [Fintype.card_fin]
      field_simp
      linear_combination -he2
    set r : Su K p f 2 := mkSU K p f (e⁻¹ • P) hrdet hriso with hr
    obtain ⟨A, hA⟩ := hnon' r
    apply hA
    have hrm : suMat r = e⁻¹ • P := suMat_mkSU hrdet hriso
    have key : P = e • suMat r := by rw [hrm, smul_smul, mul_inv_cancel₀ he0, one_smul]
    calc P * suMat A = (e • suMat r) * suMat A := by rw [← key]
      _ = e • (suMat r * suMat A * (suMat r⁻¹ * suMat r)) := by
          rw [suMat_inv_mul_suMat, Matrix.mul_one, Matrix.smul_mul]
      _ = suMat r * suMat A * suMat r⁻¹ * (e • suMat r) := by
          simp only [Matrix.mul_smul, Matrix.mul_assoc]
      _ = suMat r * suMat A * suMat r⁻¹ * P := by rw [← key]
  ·
    have hPa : P * P = a ^ 2 • 1 := by rw [ha]; exact hS1
    have hTa : T * T = a ^ 2 • 1 := by rw [ha]; exact hS2
    refine ⟨a, P, T, rfl, hn1, hI1, hPa, hPns a, hPns (-a), hI2, hTa, ?_, ?_⟩
    · intro hTe
      have := congrFun (congrFun hI2 0) 0
      rw [hTe] at this
      simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two] at this
      rw [hn1] at this
      apply h2
      linear_combination -this
    · intro hTe
      have := congrFun (congrFun hI2 0) 0
      rw [hTe] at this
      simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two] at this
      rw [hn1] at this
      apply h2
      linear_combination -this

end Arith

end CFSG.ClassicalInvolution.RouteD.SU4Pattern
