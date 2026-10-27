module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PLn
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PLs
public import CFSG.LieType.Steinberg.CentralExt.Model

public section

namespace CFSG.ComponentClassification.GSThmB.P211

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatFactsL4U4 InvClassL HBlocks

variable {F : Type} [Field F]

theorem X1_one_mul_self : (X1 (1 : F)) * X1 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X1, Matrix.mul_apply, Fin.sum_univ_four]

theorem v2_sq_sub_one_split {q : ℕ} (hq3 : 3 ≤ q) :
    padicValNat 2 (q ^ 2 - 1) = padicValNat 2 (q - 1) + padicValNat 2 (q + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have : 1 ≤ q := by omega
    zify [this, Nat.one_le_pow 2 q (by omega)]
    ring
  rw [h, padicValNat.mul (by omega) (by omega)]

theorem one_le_v2_succ {q : ℕ} (hq : Odd q) : 1 ≤ padicValNat 2 (q + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, rfl⟩ := hq
  exact one_le_padicValNat_of_dvd (by omega) ⟨k + 1, by ring⟩

section Cases

variable [Finite F] {p f : ℕ}

theorem false_of_conjAut (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (A : GL (Fin 4) F) (h1 : conjAut 4 F A ≠ 1) (h2 : conjAut 4 F A * conjAut 4 F A = 1)
    {M : Subgroup (projectiveSL 4 F)} (hM : ⁅M, M⁆ = M) (hfix : ∀ x ∈ M, conjAut 4 F A x = x)
    (hM2 : 2 ^ (2 * padicValNat 2 ((p ^ f) ^ 2 - 1)) ∣ Nat.card M) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : ringChar F ≠ 2 := LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hF
  have h2F : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
  have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [pow_zero] at hF
      exact absurd hF (Finite.one_lt_card (α := F)).ne'
    · exact h
  have hq3 : 3 ≤ p ^ f := le_trans (by have := hp.two_le; omega) (Nat.le_self_pow (by omega) p)
  set n := padicValNat 2 ((p ^ f) ^ 2 - 1) with hn
  have hn3 : 3 ≤ n := three_le_v2 hqodd hq3
  have hq0 : p ^ f ≠ 0 := by omega
  have hq2 : (p ^ f) ^ 2 - 1 ≠ 0 := by
    have : 9 ≤ (p ^ f) ^ 2 := by nlinarith
    omega
  have hAA : conjAut 4 F (A * A) * fieldAut 4 F 1 = 1 := by rw [map_one, mul_one, map_mul, h2]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ _ hAA
  have hX : (A : Matrix (Fin 4) (Fin 4) F) * A = (c : F) • 1 := by
    rw [← Units.val_mul, ← hc, GeneralLinearGroup.coe_scalar, scalar_apply, smul_one_eq_diagonal]
  have hns : ∀ a : F, (A : Matrix (Fin 4) (Fin 4) F) ≠ a • 1 := by
    intro a ha
    apply h1
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_smul] at ha
      exact (Matrix.isUnits_det_units A).ne_zero (by rw [ha, det_zero])
    have hA : A = GeneralLinearGroup.scalar (Fin 4) (Units.mk0 a ha0) := by
      apply Units.ext
      rw [ha, GeneralLinearGroup.coe_scalar, scalar_apply, Units.val_mk0, smul_one_eq_diagonal]
    rw [hA, conjAut_scalar]
  rcases classify_inv hchar hX (Units.ne_zero c) hns with
    ⟨l, hl0, -, -, P, hP⟩ | ⟨l, hl0, -, -, P, s, hs, hP⟩ | ⟨hnsq, -⟩
  ·
    let D : GL (Fin 4) F := ⟨X1 1, X1 1, X1_one_mul_self, X1_one_mul_self⟩
    have hAP : A * P = GeneralLinearGroup.scalar (Fin 4) (Units.mk0 l hl0) * (P * D) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply,
        Units.val_mk0, ← smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
      change (A : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) =
        l • ((P : Matrix (Fin 4) (Fin 4) F) * X1 1)
      rw [← hP, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hl0, one_smul]
    obtain ⟨M', hM'p, hM'c, hM'f⟩ := exists_fixed_of_frame hAP hM hfix
    have hd := two_mul_card_dvd_of_t2 h2F (D := D) rfl hM'p hM'f
    rw [hM'c, hF] at hd
    have hk : 2 ^ (2 * n + 1) ∣ 2 * Nat.card M := by
      rw [pow_succ']
      exact Nat.mul_dvd_mul_left 2 hM2
    have h0 : p ^ f * ((p ^ f) ^ 2 - 1) ≠ 0 := Nat.mul_ne_zero hq0 hq2
    have h3 := le_v2_of_dvd (pow_ne_zero 2 h0) hk hd
    rw [padicValNat.pow, v2_SL2 hqodd hq3] at h3
    omega
  ·
    let D : GL (Fin 4) F := ⟨dOne, dOne, dOne_mul_dOne, dOne_mul_dOne⟩
    have hs0 : s * l⁻¹ ≠ 0 :=
      mul_ne_zero (by rcases hs with rfl | rfl <;> norm_num) (inv_ne_zero hl0)
    have hAP : A * P = GeneralLinearGroup.scalar (Fin 4) (Units.mk0 (s * l⁻¹)⁻¹ (inv_ne_zero hs0)) *
        (P * D) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply,
        Units.val_mk0, ← smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
      change (A : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) =
        (s * l⁻¹)⁻¹ • ((P : Matrix (Fin 4) (Fin 4) F) * dOne)
      rw [← hP, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    obtain ⟨M', hM'p, hM'c, hM'f⟩ := exists_fixed_of_frame hAP hM hfix
    have hd := card_dvd_of_t1 h2F (D := D) rfl hM'p hM'f
    rw [hM'c, hF] at hd
    have hq3' : (p ^ f) ^ 3 - 1 ≠ 0 := by
      have : 27 ≤ (p ^ f) ^ 3 := by
        calc 27 = 3 ^ 3 := by norm_num
          _ ≤ (p ^ f) ^ 3 := Nat.pow_le_pow_left hq3 3
      omega
    have h0 : (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1)) ≠ 0 :=
      Nat.mul_ne_zero (pow_ne_zero 3 hq0) (Nat.mul_ne_zero hq2 hq3')
    have h3 := le_v2_of_dvd h0 hM2 hd
    rw [padicValNat.mul (pow_ne_zero 3 hq0) (Nat.mul_ne_zero hq2 hq3'), padicValNat.pow,
      v2_odd hqodd, mul_zero, zero_add, padicValNat.mul hq2 hq3',
      v2_cube_sub_one hqodd hq3] at h3
    have hsplit := v2_sq_sub_one_split hq3
    have hsucc := one_le_v2_succ hqodd
    omega
  ·
    have hsq : A ^ 2 = GeneralLinearGroup.scalar (Fin 4) c := by
      rw [sq]
      exact hc.symm
    have hd := card_dvd_of_nonsquare A c hsq hnsq hM hfix
    rw [hF] at hd
    have hq4 : (p ^ f) ^ 4 - 1 ≠ 0 := by
      have : 81 ≤ (p ^ f) ^ 4 := by
        calc 81 = 3 ^ 4 := by norm_num
          _ ≤ (p ^ f) ^ 4 := Nat.pow_le_pow_left hq3 4
      omega
    have h0 : (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) ≠ 0 := Nat.mul_ne_zero (pow_ne_zero 2 hq0) hq4
    have h3 := le_v2_of_dvd h0 hM2 hd
    rw [padicValNat.mul (pow_ne_zero 2 hq0) hq4, padicValNat.pow, v2_odd hqodd, mul_zero,
      zero_add, v2_four hqodd hq3] at h3
    omega

theorem false_of_symmetric (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (A : GL (Fin 4) F) (hA : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = A)
    {M : Subgroup (projectiveSL 4 F)} (hM : ⁅M, M⁆ = M)
    (hfix : ∀ x ∈ M, (conjAut 4 F A * dualAut 4 F) x = x)
    (hM2 : 2 ^ (2 * padicValNat 2 ((p ^ f) ^ 2 - 1)) ∣ Nat.card M) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : ringChar F ≠ 2 := LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hF
  have h2F : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
  have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [pow_zero] at hF
      exact absurd hF (Finite.one_lt_card (α := F)).ne'
    · exact h
  have hq3 : 3 ≤ p ^ f := le_trans (by have := hp.two_le; omega) (Nat.le_self_pow (by omega) p)
  set n := padicValNat 2 ((p ^ f) ^ 2 - 1) with hn
  have hq0 : p ^ f ≠ 0 := by omega
  have hq2 : (p ^ f) ^ 2 - 1 ≠ 0 := by
    have : 9 ≤ (p ^ f) ^ 2 := by nlinarith
    omega
  have hq4 : (p ^ f) ^ 4 - 1 ≠ 0 := by
    have : 81 ≤ (p ^ f) ^ 4 := by
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ (p ^ f) ^ 4 := Nat.pow_le_pow_left hq3 4
    omega
  have hd := four_mul_card_dvd_of_symmetric h2F (hF ▸ hqodd) A hA hM hfix
  rw [hF] at hd
  have hk : 2 ^ (2 * n + 2) ∣ 4 * Nat.card M := by
    rw [pow_add, mul_comm (2 ^ (2 * n))]
    exact Nat.mul_dvd_mul (by norm_num) hM2
  have h0 : (p ^ f) ^ 2 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) ≠ 0 :=
    Nat.mul_ne_zero (pow_ne_zero 2 hq0) (Nat.mul_ne_zero hq2 hq4)
  have h3 := le_v2_of_dvd h0 hk hd
  rw [padicValNat.mul (pow_ne_zero 2 hq0) (Nat.mul_ne_zero hq2 hq4), padicValNat.pow,
    v2_odd hqodd, mul_zero, zero_add, padicValNat.mul hq2 hq4, v2_four hqodd hq3] at h3
  omega

end Cases

end CFSG.ComponentClassification.GSThmB.P211
