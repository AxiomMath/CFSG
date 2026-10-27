module

public import CFSG.ClassicalInvolution.AschTight.S1911F0b

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.ClassicalInvolution.Disconnected.AschTight.S1911 CFSG.ClassicalInvolution.Asc77.AscL62
open scoped MatrixGroups

section Algebra

variable {F : Type} [Field F]

theorem exists_pow_eq_of_pow_succ_eq_one [Finite F] {m : ℕ} (hF : Nat.card F = m ^ 2)
    (hm : 2 ≤ m) {μ : F} (hμ0 : μ ≠ 0) (hμ : μ ^ (m + 1) = 1) :
    ∃ κ : F, κ ≠ 0 ∧ κ ^ m * μ = κ := by
  classical
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf γ = m ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_units, hF]
  have hfin : IsOfFinOrder γ := isOfFinOrder_of_finite γ
  obtain ⟨k, hk⟩ := hfin.mem_powers_iff_mem_zpowers.mpr (hγ (Units.mk0 μ hμ0))
  have hk' : γ ^ k = Units.mk0 μ hμ0 := hk
  have hdvd : orderOf γ ∣ k * (m + 1) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, hk']
    apply Units.ext
    simpa using hμ
  have hm2 : m ^ 2 - 1 = (m - 1) * (m + 1) := by
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  rw [hord, hm2] at hdvd
  obtain ⟨j, hj⟩ := Nat.dvd_of_mul_dvd_mul_right (by omega : 0 < m + 1) hdvd
  refine ⟨(((γ ^ j)⁻¹ : Fˣ) : F), Units.ne_zero _, ?_⟩
  have h1 : ((γ ^ j)⁻¹) ^ m * Units.mk0 μ hμ0 = (γ ^ j)⁻¹ := by
    rw [← hk', hj, mul_comm (m - 1) j, pow_mul]
    generalize γ ^ j = u
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have h2 : u⁻¹ ^ n * u ^ n = 1 := by rw [← mul_pow, inv_mul_cancel, one_pow]
    calc u⁻¹ ^ (n + 1) * u ^ n = (u⁻¹ ^ n * u ^ n) * u⁻¹ := by rw [pow_succ, mul_right_comm]
      _ = u⁻¹ := by rw [h2, one_mul]
  have h3 := congrArg Units.val h1
  simpa using h3

theorem orderOf_eq_four_of_mul_self (h2 : (2 : F) ≠ 0) (y : SL(2, F))
    (h : (y : Matrix (Fin 2) (Fin 2) F) * (y : Matrix (Fin 2) (Fin 2) F) =
      (-1 : F) • (1 : Matrix (Fin 2) (Fin 2) F)) : orderOf y = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyy : ((y * y : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      (-1 : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [Matrix.SpecialLinearGroup.coe_mul]; exact h
  have hne : ¬ y ^ 2 ^ 1 = 1 := by
    intro h1
    have h1' : y * y = 1 := by simpa [pow_two] using h1
    have h1'' := congrArg (fun z : SL(2, F) => (z : Matrix (Fin 2) (Fin 2) F)) h1'
    simp only [hyy, Matrix.SpecialLinearGroup.coe_one] at h1''
    have := congrFun (congrFun h1'' 0) 0
    simp at this
    apply h2
    linear_combination -this
  have h4 : y ^ 2 ^ (1 + 1) = 1 := by
    have e : y ^ 2 ^ (1 + 1) = (y * y) * (y * y) := by simp [pow_succ, mul_assoc]
    rw [e]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, hyy, Matrix.SpecialLinearGroup.coe_one]
    simp
  have := orderOf_eq_prime_pow (p := 2) (n := 1) hne h4
  simpa using this

theorem eq_smul_one_of_sq_eq_one (h2 : (2 : F) ≠ 0) {M : Matrix (Fin 2) (Fin 2) F}
    (hsq : M * M = 1) (hdet : M.det = 1) : ∃ a : F, M = a • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have e00 := congrFun (congrFun hsq 0) 0
  have e01 := congrFun (congrFun hsq 0) 1
  have e10 := congrFun (congrFun hsq 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  rw [Matrix.det_fin_two] at hdet
  by_cases hs : M 0 0 + M 1 1 = 0
  · exfalso
    apply h2
    have hd : M 1 1 = - M 0 0 := by linear_combination hs
    rw [hd] at hdet
    linear_combination -(e00 + hdet)
  · have hb : M 0 1 = 0 := by
      have : (M 0 0 + M 1 1) * M 0 1 = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_left hs
    have hc : M 1 0 = 0 := by
      have : (M 0 0 + M 1 1) * M 1 0 = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_left hs
    rw [hb, hc] at e00 hdet
    have ha0 : M 0 0 ≠ 0 := by
      intro h0
      rw [h0] at e00
      simp at e00
    have had : M 0 0 = M 1 1 := by
      apply mul_left_cancel₀ ha0
      linear_combination e00 - hdet
    refine ⟨M 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, had]

theorem exists_fixed_order_four [Finite F] {m : ℕ} (hF : Nat.card F = m ^ 2) (hm : 3 ≤ m)
    (hodd : Odd m) (h2 : (2 : F) ≠ 0) (σ : F ≃+* F) (hσ : ∀ x, σ x = x ^ m)
    (hσ2 : ∀ x, σ (σ x) = x) (A B : GL (Fin 2) F)
    (hA : ∀ b, semilinHom A σ (semilinHom A σ b) = b)
    (hB : ∀ b, semilinHom B 1 (semilinHom B 1 b) = b)
    (hAB : ∀ b, semilinHom A σ (semilinHom B 1 b) = semilinHom B 1 (semilinHom A σ b)) :
    ∃ y : SL(2, F), orderOf y = 4 ∧ semilinHom B 1 y = y := by
  classical
  set Am : Matrix (Fin 2) (Fin 2) F := (A : Matrix (Fin 2) (Fin 2) F) with hAm
  set Ai : Matrix (Fin 2) (Fin 2) F := ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
    with hAi
  set Bm : Matrix (Fin 2) (Fin 2) F := (B : Matrix (Fin 2) (Fin 2) F) with hBm
  set Bi : Matrix (Fin 2) (Fin 2) F := ((B⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
    with hBi
  have hAAi : Am * Ai = 1 := by rw [hAm, hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAiA : Ai * Am = 1 := by rw [hAm, hAi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hBBi : Bm * Bi = 1 := by rw [hBm, hBi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBiB : Bi * Bm = 1 := by rw [hBm, hBi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hone : (1 : Matrix (Fin 2) (Fin 2) F).map σ = 1 :=
    Matrix.map_one σ (map_zero σ) (map_one σ)
  have hB1 : ∀ b : SL(2, F), ((semilinHom B 1 b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      Bm * (b : Matrix (Fin 2) (Fin 2) F) * Bi := by
    intro b
    rw [coe_semilinHom]
    have : (b : Matrix (Fin 2) (Fin 2) F).map (⇑(1 : F ≃+* F)) =
        (b : Matrix (Fin 2) (Fin 2) F) := by
      ext i j
      simp
    rw [this]
  have hAs : ∀ b : SL(2, F), ((semilinHom A σ b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      Am * (b : Matrix (Fin 2) (Fin 2) F).map σ * Ai := fun b => coe_semilinHom A σ b
  have hmm : ∀ X : Matrix (Fin 2) (Fin 2) F, (X.map σ).map σ = X := map_map_eq σ hσ2
  obtain ⟨l, hl0, hσl, hAl⟩ := exists_mul_map_eq_smul σ hσ2 A hA
  have hAl' : Am * Am.map σ = l • (1 : Matrix (Fin 2) (Fin 2) F) := hAl
  set Pm : Matrix (Fin 2) (Fin 2) F := Am * Bm.map σ * Ai with hPm
  set Pmi : Matrix (Fin 2) (Fin 2) F := Am * Bi.map σ * Ai with hPmi
  have hPPi : Pm * Pmi = 1 := by
    calc Pm * Pmi = Am * (Bm.map σ * (Ai * Am) * Bi.map σ) * Ai := by
          simp only [hPm, hPmi, Matrix.mul_assoc]
      _ = Am * (Bm.map σ * Bi.map σ) * Ai := by rw [hAiA, Matrix.mul_one]
      _ = 1 := by rw [← Matrix.map_mul, hBBi, hone, Matrix.mul_one, hAAi]
  have hPiP : Pmi * Pm = 1 := by
    calc Pmi * Pm = Am * (Bi.map σ * (Ai * Am) * Bm.map σ) * Ai := by
          simp only [hPm, hPmi, Matrix.mul_assoc]
      _ = Am * (Bi.map σ * Bm.map σ) * Ai := by rw [hAiA, Matrix.mul_one]
      _ = 1 := by rw [← Matrix.map_mul, hBiB, hone, Matrix.mul_one, hAAi]
  have hconjmap : ∀ X : Matrix (Fin 2) (Fin 2) F, Am * (Bm * X * Bi).map σ * Ai =
      Pm * (Am * X.map σ * Ai) * Pmi := by
    intro X
    have key : ∀ Y : Matrix (Fin 2) (Fin 2) F, Ai * (Am * Y) = Y := fun Y => by
      rw [← Matrix.mul_assoc, hAiA, Matrix.one_mul]
    simp only [hPm, hPmi, Matrix.map_mul, Matrix.mul_assoc, key]
  have hPy : ∀ y : SL(2, F), Pm * (y : Matrix (Fin 2) (Fin 2) F) * Pmi =
      Bm * (y : Matrix (Fin 2) (Fin 2) F) * Bi := by
    intro y
    set x : SL(2, F) := semilinHom A σ y with hx
    have hxy : semilinHom A σ x = y := hA y
    have h1 := hAB x
    rw [hxy] at h1
    have h2 := congrArg (fun z : SL(2, F) => (z : Matrix (Fin 2) (Fin 2) F)) h1
    rw [hAs (semilinHom B 1 x), hB1 x, hB1 y] at h2
    have h3 : ((semilinHom A σ x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        (y : Matrix (Fin 2) (Fin 2) F) := by rw [hxy]
    rw [hAs x] at h3
    calc Pm * (y : Matrix (Fin 2) (Fin 2) F) * Pmi
        = Pm * (Am * (x : Matrix (Fin 2) (Fin 2) F).map σ * Ai) * Pmi := by rw [h3]
      _ = Am * (Bm * (x : Matrix (Fin 2) (Fin 2) F) * Bi).map σ * Ai := (hconjmap _).symm
      _ = Bm * (y : Matrix (Fin 2) (Fin 2) F) * Bi := h2
  have hcomm1 : ∀ y : SL(2, F), (Bi * Pm) * (y : Matrix (Fin 2) (Fin 2) F) =
      (y : Matrix (Fin 2) (Fin 2) F) * (Bi * Pm) := by
    intro y
    have h := hPy y
    generalize (y : Matrix (Fin 2) (Fin 2) F) = Y at h ⊢
    have h' : Pm * Y = Bm * Y * Bi * Pm := by
      calc Pm * Y = Pm * Y * (Pmi * Pm) := by rw [hPiP, Matrix.mul_one]
        _ = (Pm * Y * Pmi) * Pm := by simp only [Matrix.mul_assoc]
        _ = Bm * Y * Bi * Pm := by rw [h]
    calc Bi * Pm * Y = Bi * (Pm * Y) := by rw [Matrix.mul_assoc]
      _ = Bi * (Bm * Y * Bi * Pm) := by rw [h']
      _ = (Bi * Bm) * Y * (Bi * Pm) := by simp only [Matrix.mul_assoc]
      _ = Y * (Bi * Pm) := by rw [hBiB, Matrix.one_mul]
  obtain ⟨μ, hμ⟩ : ∃ μ : F, Bi * Pm = μ • (1 : Matrix (Fin 2) (Fin 2) F) :=
    ⟨_, eq_smul_one_of_commute (Bi * Pm) hcomm1⟩
  have hPmμ : Pm = μ • Bm := by
    calc Pm = Bm * (Bi * Pm) := by rw [← Matrix.mul_assoc, hBBi, Matrix.one_mul]
      _ = Bm * (μ • (1 : Matrix (Fin 2) (Fin 2) F)) := by rw [hμ]
      _ = μ • Bm := by rw [Matrix.mul_smul, Matrix.mul_one]
  have hμ0 : μ ≠ 0 := by
    intro h0
    have : Pm = 0 := by rw [hPmμ, h0, zero_smul]
    rw [this, Matrix.zero_mul] at hPPi
    exact zero_ne_one hPPi
  have hT : Ai.map σ * Ai = l⁻¹ • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have h1 : (Ai.map σ * Ai) * (Am * Am.map σ) = 1 := by
      calc (Ai.map σ * Ai) * (Am * Am.map σ) = Ai.map σ * (Ai * Am) * Am.map σ := by
            simp only [Matrix.mul_assoc]
        _ = Ai.map σ * Am.map σ := by rw [hAiA, Matrix.mul_one]
        _ = 1 := by rw [← Matrix.map_mul, hAiA, hone]
    rw [hAl', Matrix.mul_smul, Matrix.mul_one] at h1
    calc Ai.map σ * Ai = l⁻¹ • (l • (Ai.map σ * Ai)) := by
          rw [smul_smul, inv_mul_cancel₀ hl0, one_smul]
      _ = l⁻¹ • (1 : Matrix (Fin 2) (Fin 2) F) := by rw [h1]
  have hΦΦ : Am * Pm.map σ * Ai = Bm := by
    calc Am * Pm.map σ * Ai = (Am * Am.map σ) * Bm * (Ai.map σ * Ai) := by
          simp only [hPm, Matrix.map_mul, hmm, Matrix.mul_assoc]
      _ = Bm := by
          rw [hAl', hT, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one,
            smul_smul, inv_mul_cancel₀ hl0, one_smul]
  have hmapsmul : ∀ (c : F) (M : Matrix (Fin 2) (Fin 2) F), (c • M).map σ = σ c • M.map σ := by
    intro c M
    ext i j
    simp
  have hΦsmul : ∀ (c : F) (M : Matrix (Fin 2) (Fin 2) F),
      Am * (c • M).map σ * Ai = σ c • (Am * M.map σ * Ai) := by
    intro c M
    rw [hmapsmul, Matrix.mul_smul, Matrix.smul_mul]
  have hNμ : σ μ * μ = 1 := by
    have h1 : Am * Pm.map σ * Ai = (σ μ * μ) • Bm := by
      conv_lhs => rw [hPmμ]
      rw [hΦsmul, ← hPm, hPmμ, smul_smul]
    have h2 : Bm = (σ μ * μ) • Bm := by rw [← h1, hΦΦ]
    have h3 : (1 : Matrix (Fin 2) (Fin 2) F) = (σ μ * μ) • 1 := by
      calc (1 : Matrix (Fin 2) (Fin 2) F) = Bm * Bi := hBBi.symm
        _ = ((σ μ * μ) • Bm) * Bi := by rw [← h2]
        _ = (σ μ * μ) • 1 := by rw [Matrix.smul_mul, hBBi]
    have h4 := congrFun (congrFun h3 0) 0
    simpa using h4.symm
  have hμN : μ ^ (m + 1) = 1 := by
    have h1 : μ * σ μ = 1 := by rw [mul_comm]; exact hNμ
    rw [hσ] at h1
    rw [pow_succ']
    exact h1
  obtain ⟨κ, hκ0, hκ⟩ := exists_pow_eq_of_pow_succ_eq_one hF (by omega) hμ0 hμN
  have hΦB' : Am * (κ • Bm).map σ * Ai = κ • Bm := by
    rw [hΦsmul, ← hPm, hPmμ, smul_smul, hσ κ, hκ]
  have hdetAA : Am.det * Ai.det = 1 := by rw [← Matrix.det_mul, hAAi, Matrix.det_one]
  have hdetconj : ∀ X : Matrix (Fin 2) (Fin 2) F, (Am * X * Ai).det = X.det := by
    intro X
    calc (Am * X * Ai).det = X.det * (Am.det * Ai.det) := by
          rw [Matrix.det_mul, Matrix.det_mul]; ring
      _ = X.det := by rw [hdetAA, mul_one]
  have hdetmap : ∀ X : Matrix (Fin 2) (Fin 2) F, (X.map σ).det = σ X.det := by
    intro X
    have := RingHom.map_det (σ : F →+* F) X
    simpa [RingHom.mapMatrix_apply] using this.symm
  have hdσ : σ ((κ • Bm).det) = (κ • Bm).det := by
    have h1 := hdetconj ((κ • Bm).map σ)
    rw [hΦB', hdetmap] at h1
    exact h1.symm
  have hdetBm0 : Bm.det ≠ 0 := by
    intro h0
    have h1 : Bm.det * Bi.det = 1 := by rw [← Matrix.det_mul, hBBi, Matrix.det_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hdκ : (κ • Bm).det = κ ^ 2 * Bm.det := by simp
  have hd0 : (κ • Bm).det ≠ 0 := by
    rw [hdκ]
    exact mul_ne_zero (pow_ne_zero 2 hκ0) hdetBm0
  have hdm : ((κ • Bm).det) ^ m = (κ • Bm).det := by rw [← hσ, hdσ]
  obtain ⟨c, hc⟩ := exists_pow_succ_eq hF (by omega) hd0 hdm
  obtain ⟨t, ht⟩ := hodd
  have hρ : (c ^ (t + 1)) * (c ^ (t + 1)) = (κ • Bm).det := by
    rw [← pow_add, ← hc]
    congr 1
    omega
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : F, ρ = c ^ (t + 1) := ⟨_, rfl⟩
  rw [← hρdef] at hρ
  have hρ0 : ρ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hρ
    exact hd0 hρ.symm
  have hdetBm : Bm.det = (ρ * κ⁻¹) * (ρ * κ⁻¹) := by
    have h1 : κ ^ 2 * Bm.det = ρ * ρ := hdκ.symm.trans hρ.symm
    have h2 : Bm.det = ρ * ρ / κ ^ 2 := by
      field_simp
      linear_combination h1
    rw [h2]
    field_simp
  obtain ⟨r, hrdef⟩ : ∃ r : F, r = ρ * κ⁻¹ := ⟨_, rfl⟩
  rw [← hrdef] at hdetBm
  have hr0 : r ≠ 0 := by rw [hrdef]; exact mul_ne_zero hρ0 (inv_ne_zero hκ0)
  have hdetB₀ : (r⁻¹ • Bm).det = 1 := by
    rw [Matrix.det_smul, hdetBm]
    simp
    field_simp
  obtain ⟨s, hs⟩ : ∃ s : F, Bm * Bm = s • (1 : Matrix (Fin 2) (Fin 2) F) := by
    refine ⟨_, eq_smul_one_of_commute (Bm * Bm) ?_⟩
    intro b
    have h := congrArg (fun z : SL(2, F) => (z : Matrix (Fin 2) (Fin 2) F)) (hB b)
    simp only [hB1] at h
    generalize (b : Matrix (Fin 2) (Fin 2) F) = Y at h ⊢
    have hDD : (Bi * Bi) * (Bm * Bm) = 1 := by
      calc (Bi * Bi) * (Bm * Bm) = Bi * (Bi * Bm) * Bm := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hBiB, Matrix.mul_one, hBiB]
    calc Bm * Bm * Y = Bm * Bm * Y * ((Bi * Bi) * (Bm * Bm)) := by rw [hDD, Matrix.mul_one]
      _ = (Bm * (Bm * Y * Bi) * Bi) * (Bm * Bm) := by simp only [Matrix.mul_assoc]
      _ = Y * (Bm * Bm) := by rw [h]
  have hB₀2 : (r⁻¹ • Bm) * (r⁻¹ • Bm) = (r⁻¹ * (r⁻¹ * s)) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hs, smul_smul, smul_smul, mul_assoc]
  have hs'sq : (r⁻¹ * (r⁻¹ * s)) * (r⁻¹ * (r⁻¹ * s)) = 1 := by
    have h := congrArg Matrix.det hB₀2
    rw [Matrix.det_mul, hdetB₀, Matrix.det_smul, Matrix.det_one] at h
    simp at h
    linear_combination -h
  have hyfix : Bm * (r⁻¹ • Bm) * Bi = r⁻¹ • Bm := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hBBi, Matrix.mul_one]
  obtain ⟨y₁, hy₁⟩ : ∃ y₁ : SL(2, F), (y₁ : Matrix (Fin 2) (Fin 2) F) = r⁻¹ • Bm :=
    ⟨⟨r⁻¹ • Bm, hdetB₀⟩, rfl⟩
  have hy₁fix : semilinHom B 1 y₁ = y₁ := by
    apply Subtype.ext
    rw [hB1, hy₁]
    exact hyfix
  rcases mul_self_eq_one_iff.mp hs'sq with h1 | h1
  ·
    have hB₀sq : (r⁻¹ • Bm) * (r⁻¹ • Bm) = 1 := by rw [hB₀2, h1, one_smul]
    obtain ⟨a, ha⟩ := eq_smul_one_of_sq_eq_one h2 hB₀sq hdetB₀
    have hBs : Bm = (r * a) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      calc Bm = r • (r⁻¹ • Bm) := by rw [smul_smul, mul_inv_cancel₀ hr0, one_smul]
        _ = (r * a) • 1 := by rw [ha, smul_smul]
    have hBcomm : ∀ Y : Matrix (Fin 2) (Fin 2) F, Bm * Y * Bi = Y := by
      intro Y
      have h3 : Bm * Y = Y * Bm := by
        rw [hBs]
        simp
      rw [h3, Matrix.mul_assoc, hBBi, Matrix.mul_one]
    have : Fintype F := Fintype.ofFinite F
    have hiq : IsSquare (-1 : F) := by
      rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hF, ht]
      have h3 : (2 * t + 1) ^ 2 = 4 * (t * t + t) + 1 := by ring
      rw [h3]
      generalize t * t + t = u
      omega
    obtain ⟨i, hi⟩ := hiq
    obtain ⟨y₀, hy₀⟩ : ∃ y₀ : SL(2, F),
        (y₀ : Matrix (Fin 2) (Fin 2) F) = !![i, 0; 0, -i] :=
      ⟨⟨!![i, 0; 0, -i], by simp [Matrix.det_fin_two]; linear_combination hi⟩, rfl⟩
    refine ⟨y₀, ?_, ?_⟩
    · apply orderOf_eq_four_of_mul_self h2
      rw [hy₀]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hi]
    · apply Subtype.ext
      rw [hB1]
      exact hBcomm _
  · refine ⟨y₁, ?_, hy₁fix⟩
    apply orderOf_eq_four_of_mul_self h2
    rw [hy₁, hB₀2, h1]

end Algebra

end CFSG.ClassicalInvolution.Asc77.C25V
