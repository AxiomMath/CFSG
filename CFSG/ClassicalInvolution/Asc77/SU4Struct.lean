module

public import CFSG.ClassicalInvolution.Models.UnitaryFrames.Chart
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarCommutantSpace

public section

namespace CFSG.ClassicalInvolution.RouteD.SU4Pattern

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Models

section BlockDiag

variable {K : Type} [Field K]

@[expose] def BD (X Y : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  blockMat 4 0 X * blockMat 4 2 Y

theorem BD_eq (X Y : Matrix (Fin 2) (Fin 2) K) :
    BD X Y =
      !![X 0 0, X 0 1, 0, 0; X 1 0, X 1 1, 0, 0; 0, 0, Y 0 0, Y 0 1; 0, 0, Y 1 0, Y 1 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [BD, Matrix.mul_apply, blockMat_apply, Fin.sum_univ_four]

theorem BD_mul (X Y X' Y' : Matrix (Fin 2) (Fin 2) K) :
    BD X Y * BD X' Y' = BD (X * X') (Y * Y') := by
  rw [BD_eq, BD_eq, BD_eq]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem BD_inj {X Y X' Y' : Matrix (Fin 2) (Fin 2) K} (h : BD X Y = BD X' Y') :
    X = X' ∧ Y = Y' := by
  rw [BD_eq, BD_eq] at h
  constructor
  · ext a b
    fin_cases a <;> fin_cases b
    · simpa using congrFun (congrFun h 0) 0
    · simpa using congrFun (congrFun h 0) 1
    · simpa using congrFun (congrFun h 1) 0
    · simpa using congrFun (congrFun h 1) 1
  · ext a b
    fin_cases a <;> fin_cases b
    · simpa using congrFun (congrFun h 2) 2
    · simpa using congrFun (congrFun h 2) 3
    · simpa using congrFun (congrFun h 3) 2
    · simpa using congrFun (congrFun h 3) 3

theorem BD_one : BD (1 : Matrix (Fin 2) (Fin 2) K) 1 = 1 := by
  rw [BD_eq]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem BD_smul_one (c : K) : BD (c • (1 : Matrix (Fin 2) (Fin 2) K)) (c • 1) = c • 1 := by
  rw [BD_eq]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem conjTr_BD (σ : K ≃+* K) (X Y : Matrix (Fin 2) (Fin 2) K) :
    conjTr σ (BD X Y) = BD (conjTr σ X) (conjTr σ Y) := by
  rw [BD_eq, BD_eq]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [conjTr]

theorem det_BD (X Y : Matrix (Fin 2) (Fin 2) K) : (BD X Y).det = X.det * Y.det := by
  unfold BD
  rw [det_mul, det_blockMat (by omega), det_blockMat (by omega)]

end BlockDiag

section Commutant

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_norm_one_ne (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    ∃ u : K, unitaryInvolution K p f u * u = 1 ∧ unitaryInvolution K p f u ≠ u := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨c, hc, hcf⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.exists_norm_one_not_fixed h hp2
  have hb : ∀ x, h.bar x = unitaryInvolution K p f x := fun x => by
    rw [unitaryInvolution_apply, h.bar_apply]
  refine ⟨c, by rw [← hb]; exact hc, fun he => hcf ?_⟩
  rw [h.mem_fixedField, hb]
  exact he

theorem commutant_blockSu2 (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (B : Matrix (Fin 4) (Fin 4) K)
    (hB : ∀ A : Su K p f 2, B * blockMat 4 0 (suMat A) = blockMat 4 0 (suMat A) * B) :
    B = BD (B 0 0 • (1 : Matrix (Fin 2) (Fin 2) K)) !![B 2 2, B 2 3; B 3 2, B 3 3] := by
  obtain ⟨u, hu, hne⟩ := exists_norm_one_ne hK hp2 hq
  set σ := unitaryInvolution K p f with hσ
  have hσσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hK
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
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
  have hdet2 : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.det_fin_two_of]
    simp
  have hiso2 : conjTr σ (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) *
      (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two]
  have h1 := hB (mkSU K p f _ hdet1 hiso1)
  have h2 := hB (mkSU K p f _ hdet2 hiso2)
  rw [suMat_mkSU] at h1 h2
  have e01 := congrFun (congrFun h1 0) 1
  have e10 := congrFun (congrFun h1 1) 0
  have e02 := congrFun (congrFun h1 0) 2
  have e03 := congrFun (congrFun h1 0) 3
  have e20 := congrFun (congrFun h1 2) 0
  have e30 := congrFun (congrFun h1 3) 0
  have e12 := congrFun (congrFun h1 1) 2
  have e13 := congrFun (congrFun h1 1) 3
  have e21 := congrFun (congrFun h1 2) 1
  have e31 := congrFun (congrFun h1 3) 1
  have f01 := congrFun (congrFun h2 0) 1
  simp [Matrix.mul_apply, blockMat_apply, Fin.sum_univ_four] at e01 e10 e02 e03 e20 e30
  simp [Matrix.mul_apply, blockMat_apply, Fin.sum_univ_four] at e12 e13 e21 e31 f01
  have z01 : B 0 1 = 0 := by
    have : B 0 1 * (σ u - u) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
  have z10 : B 1 0 = 0 := by
    have : B 1 0 * (u - σ u) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr (Ne.symm hne))
  have z02 : B 0 2 = 0 := by
    have : B 0 2 * (1 - u) = 0 := by linear_combination e02
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr (Ne.symm hu1))
  have z03 : B 0 3 = 0 := by
    have : B 0 3 * (1 - u) = 0 := by linear_combination e03
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr (Ne.symm hu1))
  have z20 : B 2 0 = 0 := by
    have : B 2 0 * (u - 1) = 0 := by linear_combination e20
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hu1)
  have z30 : B 3 0 = 0 := by
    have : B 3 0 * (u - 1) = 0 := by linear_combination e30
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hu1)
  have z12 : B 1 2 = 0 := by
    have : B 1 2 * (1 - σ u) = 0 := by linear_combination e12
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr (Ne.symm hu1'))
  have z13 : B 1 3 = 0 := by
    have : B 1 3 * (1 - σ u) = 0 := by linear_combination e13
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr (Ne.symm hu1'))
  have z21 : B 2 1 = 0 := by
    have : B 2 1 * (σ u - 1) = 0 := by linear_combination e21
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hu1')
  have z31 : B 3 1 = 0 := by
    have : B 3 1 * (σ u - 1) = 0 := by linear_combination e31
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hu1')
  rw [BD_eq]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [z01, z10, z02, z03, z20, z30, z12, z13, z21, z31, ← f01]

end Commutant

section Arith

theorem scalar_block_false {K : Type} [Field K] (hK2 : (2 : K) ≠ 0) {q : ℕ} (hq4 : q % 4 = 1)
    {c d D : K} (hc : c ^ (q + 1) = 1) (hD : D = c ^ 2 * d ^ 2) (hd : d ^ 2 = -c ^ 2)
    (hDn : D ^ ((q + 1) / 2) = 1) : False := by
  obtain ⟨j, hj⟩ : ∃ j, q = 4 * j + 1 := ⟨q / 4, by omega⟩
  have hn : (q + 1) / 2 = 2 * j + 1 := by omega
  have h1 : D = -(c ^ 4) := by rw [hD, hd]; ring
  have h2 : c ^ (4 * (2 * j + 1)) = 1 := by
    have : 4 * (2 * j + 1) = (q + 1) * 2 := by omega
    rw [this, pow_mul, hc, one_pow]
  rw [hn, h1, neg_pow, ← pow_mul, h2, mul_one] at hDn
  rw [Odd.neg_one_pow ⟨j, rfl⟩] at hDn
  apply hK2
  linear_combination -hDn

theorem mul_map_pow_half {K : Type} [Field K] (φ : K →+* K) {δ : K} {m : ℕ}
    (h : δ ^ (2 * m) = 1) : (δ * φ δ) ^ m = 1 := by
  have h1 : (δ ^ m) * (δ ^ m) = 1 := by rw [← pow_add, ← two_mul]; exact h
  rcases mul_self_eq_one_iff.mp h1 with h2 | h2
  · rw [mul_pow, ← map_pow, h2, map_one, one_mul]
  · rw [mul_pow, ← map_pow, h2, map_neg, map_one, neg_mul_neg, mul_one]

end Arith

section BlockData

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem norm_pow_eq_one {c : K} (h : unitaryInvolution K p f c * c = 1) :
    c ^ (p ^ f + 1) = 1 := by
  rw [unitaryInvolution_apply, ← pow_succ] at h
  exact h

theorem block_data (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hq4 : p ^ f % 4 = 1) {ι : K} (hι : ι * ι = -1) (hσι : unitaryInvolution K p f ι = ι)
    (r : Su K p f 2) (hr2 : suMat r * suMat r = -1) {H : Matrix (Fin 4) (Fin 4) K}
    (hcomm : ∀ A : Su K p f 2, H * blockMat 4 0 (suMat A) =
      blockMat 4 0 (suMat r * suMat A * suMat r⁻¹) * H)
    (hiso : conjTr (unitaryInvolution K p f) H * H = 1) (hsq : ∃ s : K, H * H = s • 1)
    (hdet : H.det ^ ((p ^ f + 1) / 2) = 1) :
    ∃ (a : K) (H₁ H₂ : Matrix (Fin 2) (Fin 2) K), H = BD H₁ H₂ ∧
      unitaryInvolution K p f a * a = -1 ∧
      conjTr (unitaryInvolution K p f) H₁ * H₁ = 1 ∧ H₁ * H₁ = a ^ 2 • 1 ∧ H₁ ≠ a • 1 ∧
      H₁ ≠ (-a) • 1 ∧ conjTr (unitaryInvolution K p f) H₂ * H₂ = 1 ∧ H₂ * H₂ = a ^ 2 • 1 ∧
      H₂ ≠ a • 1 ∧ H₂ ≠ (-a) • 1 := by
  set σ := unitaryInvolution K p f with hσ
  have h2 : (2 : K) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_charP_ne_two hp2
  obtain ⟨s, hs⟩ := hsq
  have hRdet : (suMat r).det = 1 := det_suMat r
  have hRiso : conjTr σ (suMat r) * suMat r = 1 := r.2.2
  set B : Matrix (Fin 4) (Fin 4) K := blockMat 4 0 (suMat r⁻¹) * H with hB
  have hrinv' : blockMat 4 0 (suMat r) * blockMat 4 0 (suMat r⁻¹) = 1 := by
    rw [← blockMat_mul (by omega), suMat_mul_suMat_inv, blockMat_one]
  have hBcomm : ∀ A : Su K p f 2, B * blockMat 4 0 (suMat A) = blockMat 4 0 (suMat A) * B := by
    intro A
    have e : suMat r⁻¹ * (suMat r * suMat A * suMat r⁻¹) = suMat A * suMat r⁻¹ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, suMat_inv_mul_suMat, Matrix.one_mul]
    calc B * blockMat 4 0 (suMat A)
        = blockMat 4 0 (suMat r⁻¹) * (H * blockMat 4 0 (suMat A)) := by
          rw [hB, Matrix.mul_assoc]
      _ = blockMat 4 0 (suMat r⁻¹) *
            (blockMat 4 0 (suMat r * suMat A * suMat r⁻¹) * H) := by rw [hcomm A]
      _ = (blockMat 4 0 (suMat r⁻¹) * blockMat 4 0 (suMat r * suMat A * suMat r⁻¹)) * H :=
          (Matrix.mul_assoc _ _ _).symm
      _ = blockMat 4 0 (suMat A * suMat r⁻¹) * H := by rw [← blockMat_mul (by omega), e]
      _ = blockMat 4 0 (suMat A) * B := by
          rw [blockMat_mul (by omega), hB, Matrix.mul_assoc]
  have hBform := commutant_blockSu2 hK hp2 hq B hBcomm
  set c : K := B 0 0 with hc
  set B₂ : Matrix (Fin 2) (Fin 2) K := !![B 2 2, B 2 3; B 3 2, B 3 3] with hB₂
  have hHform : H = BD (c • suMat r) B₂ := by
    have h1 : H = blockMat 4 0 (suMat r) * B := by
      rw [hB, ← Matrix.mul_assoc, hrinv', Matrix.one_mul]
    rw [h1, hBform]
    unfold BD
    rw [← Matrix.mul_assoc, ← blockMat_mul (by omega), Matrix.mul_smul, Matrix.mul_one]
  clear_value c B₂
  clear hBform hB hBcomm
  subst hHform
  have hconjsmul : ∀ (x : K) (A : Matrix (Fin 2) (Fin 2) K), conjTr σ (x • A) = σ x • conjTr σ A :=
    fun x A => by ext i j; simp [conjTr]
  rw [conjTr_BD, BD_mul, ← BD_one] at hiso
  obtain ⟨hI1, hI2⟩ := BD_inj hiso
  have hcn : σ c * c = 1 := by
    rw [hconjsmul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hRiso] at hI1
    have := congrFun (congrFun hI1 0) 0
    simpa using this
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hcn
  rw [BD_mul, ← BD_smul_one] at hs
  obtain ⟨hS1, hS2⟩ := BD_inj hs
  have hRR : suMat r * suMat r = -1 := hr2
  have hs' : s = -c ^ 2 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hRR] at hS1
    have := congrFun (congrFun hS1 0) 0
    simp at this
    linear_combination -this
  have hdetR : ∀ x : K, (x • (1 : Matrix (Fin 2) (Fin 2) K)).det = x ^ 2 := fun x => by
    simp
  have ha : σ (c * ι) * (c * ι) = -1 := by
    rw [map_mul, hσι]
    linear_combination (ι * ι) * hcn + hι
  have hH1sq : (c • suMat r) * (c • suMat r) = (c * ι) ^ 2 • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hRR]
    have : (c * ι) ^ 2 = -(c * c) := by linear_combination c ^ 2 * hι
    rw [this, neg_smul, ← neg_one_smul K (1 : Matrix (Fin 2) (Fin 2) K)]
    simp
  have hH2sq : B₂ * B₂ = (c * ι) ^ 2 • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have : (c * ι) ^ 2 = s := by rw [hs']; linear_combination c ^ 2 * hι
    rw [this]
    exact hS2
  have hnot_scalar : ∀ d : K, B₂ ≠ d • 1 := by
    intro d hd
    rw [hd, smul_mul_smul_comm, Matrix.one_mul] at hS2
    have hd2 : d ^ 2 = -c ^ 2 := by
      have := congrFun (congrFun hS2 0) 0
      simp at this
      rw [hs'] at this
      linear_combination this
    have hdetH : (BD (c • suMat r) B₂).det = c ^ 2 * d ^ 2 := by
      rw [det_BD, Matrix.det_smul, hRdet, hd, hdetR]
      simp
    exact scalar_block_false h2 hq4 (norm_pow_eq_one hcn) hdetH hd2 hdet
  refine ⟨c * ι, c • suMat r, B₂, rfl, ha, hI1, hH1sq, ?_, ?_, hI2, hH2sq, fun h => hnot_scalar _ h,
    fun h => hnot_scalar _ h⟩
  · intro h
    have h' : suMat r = ι • 1 := by
      calc suMat r = c⁻¹ • (c • suMat r) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
        _ = c⁻¹ • ((c * ι) • (1 : Matrix (Fin 2) (Fin 2) K)) := by rw [h]
        _ = ι • 1 := by rw [smul_smul, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
    have := congrArg Matrix.det h'
    rw [hRdet, hdetR] at this
    apply h2
    linear_combination this + hι
  · intro h
    have h' : suMat r = (-ι) • 1 := by
      calc suMat r = c⁻¹ • (c • suMat r) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
        _ = c⁻¹ • ((-(c * ι)) • (1 : Matrix (Fin 2) (Fin 2) K)) := by rw [h]
        _ = (-ι) • 1 := by
          rw [smul_smul]
          congr 1
          field_simp
    have := congrArg Matrix.det h'
    rw [hRdet, hdetR] at this
    apply h2
    linear_combination this + hι

end BlockData

end CFSG.ClassicalInvolution.RouteD.SU4Pattern
