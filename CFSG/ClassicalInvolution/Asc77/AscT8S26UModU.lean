module

public import CFSG.ClassicalInvolution.Asc77.AscT8S26UModUA
public import CFSG.ClassicalInvolution.Asc77.AscT8S26UModL
public import CFSG.RankThree.PartTwo.KFacts.AutPSUFaithful

public section

namespace CFSG.ClassicalInvolution.Asc77

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open scoped MatrixGroups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem s26_mat2_neg_one (h2 : (2 : K) ≠ 0) {y : Matrix (Fin 2) (Fin 2) K}
    (hy2 : y * y = 1) (hdet : y.det = 1) (hy1 : y ≠ 1) : y = -1 := by
  rw [Matrix.eta_fin_two y] at hy2 hdet hy1 ⊢
  have e00 := congrFun (congrFun hy2 0) 0
  have e01 := congrFun (congrFun hy2 0) 1
  have e10 := congrFun (congrFun hy2 1) 0
  have e11 := congrFun (congrFun hy2 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  rw [Matrix.det_fin_two] at hdet
  simp at hdet
  set a := y 0 0
  set b := y 0 1
  set c := y 1 0
  set d := y 1 1
  by_cases ht : a + d = 0
  · exfalso
    apply h2
    have hd : d = -a := by linear_combination ht
    rw [hd] at hdet
    linear_combination -hdet - e00
  · have hb : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right ht
    have hc : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right ht
    rw [hb, hc] at hdet e00 e11
    have had : a = d := by
      have : a * (d - a) = 0 := by linear_combination hdet - e00
      rcases mul_eq_zero.mp this with h' | h'
      · exfalso
        rw [h'] at hdet
        simp at hdet
      · linear_combination -h'
    have ha2 : a * a = 1 := by linear_combination e00
    rcases mul_self_eq_one_iff.mp ha2 with ha1 | ha1
    · exfalso
      apply hy1
      rw [hb, hc, ← had, ha1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · rw [hb, hc, ← had, ha1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp


@[expose] def s26Blk (X : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  !![X 0 0, X 0 1, 0; X 1 0, X 1 1, 0; 0, 0, 1]

theorem s26Blk_mul (X Y : Matrix (Fin 2) (Fin 2) K) :
    s26Blk (X * Y) = s26Blk X * s26Blk Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s26Blk, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem s26Blk_one : s26Blk (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s26Blk]

theorem s26Blk_pow (X : Matrix (Fin 2) (Fin 2) K) (k : ℕ) :
    s26Blk (X ^ k) = (s26Blk X) ^ k := by
  induction k with
  | zero => simp [s26Blk_one]
  | succ k ih => rw [pow_succ, pow_succ, s26Blk_mul, ih]

theorem s26Blk_injective : Function.Injective (s26Blk : Matrix (Fin 2) (Fin 2) K → _) := by
  intro X Y hXY
  have e00 := congrFun (congrFun hXY 0) 0
  have e01 := congrFun (congrFun hXY 0) 1
  have e10 := congrFun (congrFun hXY 1) 0
  have e11 := congrFun (congrFun hXY 1) 1
  simp [s26Blk] at e00 e01 e10 e11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11]

theorem s26Blk_neg_one : s26Blk (-1 : Matrix (Fin 2) (Fin 2) K) = s26xM := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s26Blk, s26xM]

theorem s26R0_eq_blk (a b c d : K) : s26R0 a b c d = s26Blk !![a, b; c, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s26Blk, s26R0]

theorem s26_pow_form {y : ℕ} (hy : Odd y) (m : ℕ) :
    ∃ t : ℕ, y ^ 2 ^ (m + 1) = 1 + 2 ^ (m + 3) * t := by
  induction m with
  | zero =>
    obtain ⟨j, rfl⟩ := hy
    obtain ⟨u, hu⟩ := Nat.even_mul_succ_self j
    refine ⟨u, ?_⟩
    calc (2 * j + 1) ^ 2 ^ (0 + 1) = 1 + 4 * (j * (j + 1)) := by ring
      _ = 1 + 2 ^ (0 + 3) * u := by rw [hu]; ring
  | succ m ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t + 2 ^ (m + 2) * t ^ 2, ?_⟩
    calc y ^ 2 ^ (m + 1 + 1) = (y ^ 2 ^ (m + 1)) ^ 2 := by rw [pow_succ 2 (m + 1), pow_mul]
      _ = (1 + 2 ^ (m + 3) * t) ^ 2 := by rw [ht]
      _ = 1 + 2 ^ (m + 1 + 3) * (t + 2 ^ (m + 2) * t ^ 2) := by ring

include h in
theorem s26U_sigma_pow [Finite K] {n : ℕ} (hp2 : p ≠ 2) (hmax : ¬ 2 ^ (n + 3) ∣ (p ^ f) ^ 2 - 1)
    {σ : K ≃+* K} (h1 : σ ^ 2 ^ (n + 1) = 1) : σ ^ 2 ^ n = 1 := by
  by_contra h0
  have hord : orderOf σ = 2 ^ (n + 1) := orderOf_eq_prime_pow h0 h1
  have hf : 1 ≤ 2 * f := by
    have := h.one_le
    omega
  obtain ⟨σ₀, -, -, -, hcard, -⟩ := finite_field_automorphism_fixed_field_cardinality h.prime hf
    h.card
  have hdvd : 2 ^ (n + 1) ∣ 2 * f := by
    rw [← hcard, ← hord]
    exact orderOf_dvd_natCard σ
  rw [pow_succ'] at hdvd
  obtain ⟨g, hg⟩ := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) hdvd
  have hodd : Odd (p ^ g) := (h.prime.odd_of_ne_two hp2).pow
  obtain ⟨t, ht⟩ := s26_pow_form hodd n
  apply hmax
  have e : (p ^ f) ^ 2 = (p ^ g) ^ 2 ^ (n + 1) := by
    rw [← pow_mul, ← pow_mul, hg]
    congr 1
    ring
  rw [e, ht]
  simp


include h in
theorem s26U_pow (A : unitaryIsom3 h) (σ : K ≃+* K) (k : ℕ) :
    ∃ N : unitaryIsom3 h, (psuConj h A * psuField h σ) ^ k = psuConj h N * psuField h (σ ^ k) := by
  induction k with
  | zero => exact ⟨1, by simp⟩
  | succ k ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨N * ⟨glAut (σ ^ k) A, glAut_mem_unitaryIsom3 (σ ^ k) A.2⟩, ?_⟩
    have h1 := psuField_mul_psuConj_mul_inv (h := h) (σ ^ k) A
    have h2 : psuField h (σ ^ k) * psuConj h A =
        psuConj h ⟨glAut (σ ^ k) A, glAut_mem_unitaryIsom3 (σ ^ k) A.2⟩ * psuField h (σ ^ k) := by
      rw [← h1]
      group
    rw [pow_succ, hN]
    calc psuConj h N * psuField h (σ ^ k) * (psuConj h A * psuField h σ)
        = psuConj h N * (psuField h (σ ^ k) * psuConj h A) * psuField h σ := by group
      _ = psuConj h N * (psuConj h ⟨glAut (σ ^ k) A, glAut_mem_unitaryIsom3 (σ ^ k) A.2⟩ *
            psuField h (σ ^ k)) * psuField h σ := by rw [h2]
      _ = psuConj h (N * ⟨glAut (σ ^ k) A, glAut_mem_unitaryIsom3 (σ ^ k) A.2⟩) *
            psuField h (σ ^ k * σ) := by
        rw [map_mul, map_mul]
        group
      _ = _ := by rw [pow_succ]

include h in
theorem s26U_comm_of_conj_fix (A : unitaryIsom3 h) (g : unitarySU p f K 3)
    (hg : psuConj h A (unitaryProj h 3 g) = unitaryProj h 3 g) :
    ∃ c : Kˣ, ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (c : K) • (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  have h1 : ((suConj h A g : unitarySU p f K 3) : unitaryPSU h 3) = (g : unitaryPSU h 3) := hg
  have h2 := (QuotientGroup.eq_iff_div_mem).mp h1
  obtain ⟨c, -, -, hc⟩ := mem_unitaryScalars.mp h2
  refine ⟨c, ?_⟩
  have hc' : (A : GL (Fin 3) K) * (g : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ *
      (g : GL (Fin 3) K)⁻¹ = GeneralLinearGroup.scalar (Fin 3) c := by
    have := hc
    rw [Subgroup.coe_div, coe_suConj] at this
    simpa [div_eq_mul_inv] using this
  have hGL : (A : GL (Fin 3) K) * (g : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) c *
      ((g : GL (Fin 3) K) * (A : GL (Fin 3) K)) := by
    calc (A : GL (Fin 3) K) * (g : GL (Fin 3) K)
        = ((A : GL (Fin 3) K) * g * (A : GL (Fin 3) K)⁻¹ * (g : GL (Fin 3) K)⁻¹) *
          ((g : GL (Fin 3) K) * (A : GL (Fin 3) K)) := by group
      _ = _ := by rw [hc']
  have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hGL
  simpa [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul] using this


theorem s26U_xM_sq : (s26xM : Matrix (Fin 3) (Fin 3) K) * s26xM = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s26xM, Matrix.mul_apply, Fin.sum_univ_three]

include h in
theorem s26U_psuConj_scalar (A : unitaryIsom3 h) (m : K)
    (hA : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = m • (1 : Matrix (Fin 3) (Fin 3) K)) :
    psuConj h A = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [psuConj_mk]
    show ((suConj h A g : unitarySU p f K 3) : unitaryPSU h 3) = (g : unitaryPSU h 3)
    congr 1
    apply Subtype.ext
    rw [coe_suConj]
    have hcomm : (A : GL (Fin 3) K) * (g : GL (Fin 3) K) =
        (g : GL (Fin 3) K) * (A : GL (Fin 3) K) :=
      Units.ext (by
        simp only [Units.val_mul]
        rw [hA, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one])
    calc (A : GL (Fin 3) K) * (g : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹
        = (g : GL (Fin 3) K) * (A : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ := by rw [hcomm]
      _ = (g : GL (Fin 3) K) := by group

include h in
theorem s26U_psuConj_xN (A : unitaryIsom3 h) {m : K} (hm : m ≠ 0) (xr : unitarySU p f K 3)
    (hxr : ((xr : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = s26xM) (hxr2 : xr * xr = 1)
    (hA : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = m • s26xM) :
    psuConj h A = MulAut.conj (unitaryProj h 3 xr) := by
  have hxinv : ((xr : GL (Fin 3) K))⁻¹ = (xr : GL (Fin 3) K) :=
    (inv_eq_of_mul_eq_one_right (congrArg (fun y : unitarySU p f K 3 => (y : GL (Fin 3) K)) hxr2))
  ext x
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [psuConj_mk]
    show ((suConj h A g : unitarySU p f K 3) : unitaryPSU h 3) =
      ((xr * g * xr⁻¹ : unitarySU p f K 3) : unitaryPSU h 3)
    congr 1
    apply Subtype.ext
    have hcinv : ((xr⁻¹ : unitarySU p f K 3) : GL (Fin 3) K) = (xr : GL (Fin 3) K)⁻¹ := rfl
    have hAinv : (((A⁻¹ : unitaryIsom3 h) : GL (Fin 3) K)) = ((A : GL (Fin 3) K))⁻¹ := rfl
    rw [coe_suConj, Subgroup.coe_mul, Subgroup.coe_mul, hcinv, hxinv, hAinv]
    apply Units.ext
    set N : Matrix (Fin 3) (Fin 3) K :=
      ((((A : GL (Fin 3) K))⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hN
    have hMN : (m • (s26xM : Matrix (Fin 3) (Fin 3) K)) * N = 1 := by
      rw [← hA, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h1 : (s26xM : Matrix (Fin 3) (Fin 3) K) * N = m⁻¹ • (1 : Matrix (Fin 3) (Fin 3) K) := by
      calc (s26xM : Matrix (Fin 3) (Fin 3) K) * N
          = m⁻¹ • (m • ((s26xM : Matrix (Fin 3) (Fin 3) K) * N)) := by
            rw [smul_smul, inv_mul_cancel₀ hm, one_smul]
        _ = m⁻¹ • (1 : Matrix (Fin 3) (Fin 3) K) := by rw [← Matrix.smul_mul, hMN]
    have h2 : N = m⁻¹ • (s26xM : Matrix (Fin 3) (Fin 3) K) := by
      calc N = (s26xM * s26xM : Matrix (Fin 3) (Fin 3) K) * N := by
            rw [s26U_xM_sq, Matrix.one_mul]
        _ = (s26xM : Matrix (Fin 3) (Fin 3) K) * ((s26xM : Matrix (Fin 3) (Fin 3) K) * N) := by
            rw [Matrix.mul_assoc]
        _ = m⁻¹ • (s26xM : Matrix (Fin 3) (Fin 3) K) := by
            rw [h1, Matrix.mul_smul, Matrix.mul_one]
    simp only [Units.val_mul]
    rw [hA, hxr, ← hN, h2]
    simp [smul_smul, hm]


include h in
theorem s26_psu_main [Finite K] (hodd : Odd (Nat.card K)) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hq1 : p ^ f % 4 = 1) {n : ℕ} (hmax : ¬ 2 ^ (n + 3) ∣ (p ^ f) ^ 2 - 1) (hn : 1 ≤ n)
    (φ : MulAut (unitaryPSU h 3)) (hφ : φ ^ 2 ^ (n + 1) = 1)
    {r₀ : unitarySU p f K 3} {a b c d : K}
    (hr₀m : ((r₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = s26R0 a b c d)
    (hr1 : r₀ ^ 2 ^ (n + 1) = 1) (hr0 : r₀ ^ 2 ^ n ≠ 1)
    (hfix : φ (unitaryProj h 3 r₀) = unitaryProj h 3 r₀) :
    φ ^ 2 ^ n = 1 ∨ φ ^ 2 ^ n = MulAut.conj (unitaryProj h 3 (r₀ ^ 2 ^ n)) := by
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have hq2 : 2 < p ^ f := by omega
  obtain ⟨hdet3, hunit3⟩ := (mem_unitarySU_iff h).mp r₀.2
  rw [hr₀m] at hdet3 hunit3
  have hdet : a * d - b * c = 1 := by
    simpa [Matrix.det_fin_three, s26R0] using hdet3
  have E11 := congrFun (congrFun hunit3 0) 0
  have E12 := congrFun (congrFun hunit3 0) 1
  have E21 := congrFun (congrFun hunit3 1) 0
  have E22 := congrFun (congrFun hunit3 1) 1
  simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Fin.sum_univ_three,
    s26R0] at E11 E12 E21 E22
  have ha : h.bar a = d := by
    linear_combination (-(h.bar a)) * hdet + (-c) * E12 + d * E11
  have hb : h.bar b = -c := by
    linear_combination (-(h.bar b)) * hdet + d * E21 - c * E22
  have hpowM : ∀ k : ℕ, (((r₀ ^ k : unitarySU p f K 3) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = s26Blk ((!![a, b; c, d] : Matrix (Fin 2) (Fin 2) K) ^ k) := by
    intro k
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hr₀m, s26R0_eq_blk, s26Blk_pow]
  have hA1 : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) K) ^ 2 ^ (n + 1) = 1 := by
    apply s26Blk_injective
    rw [← hpowM, hr1, s26Blk_one]
    rfl
  have hA0 : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) K) ^ 2 ^ n ≠ 1 := by
    intro hh
    apply hr0
    apply Subtype.ext
    apply Units.ext
    rw [hpowM, hh, s26Blk_one]
    rfl
  have hneg : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) K) ^ 2 ^ n = -1 := by
    apply s26_mat2_neg_one h2
    · rw [← pow_add, ← two_mul, ← pow_succ']
      exact hA1
    · rw [Matrix.det_pow, Matrix.det_fin_two_of]
      simp [hdet]
    · exact hA0
  have hxr : (((r₀ ^ 2 ^ n : unitarySU p f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      s26xM := by
    rw [hpowM, hneg, s26Blk_neg_one]
  have hxr2 : (r₀ ^ 2 ^ n) * (r₀ ^ 2 ^ n) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ']
    exact hr1
  obtain ⟨s₀, hs₀, hs₀sq, hs₀0, hnd⟩ := s26U_split_data h hodd hq1 hn hdet ha hneg
  obtain ⟨A, σ, hAσ⟩ := exists_psuConj_mul_psuField hq2 φ
  obtain ⟨N, hN⟩ := s26U_pow h A σ (2 ^ (n + 1))
  have hσ1 : σ ^ 2 ^ (n + 1) = 1 := by
    have : psuConj h N * psuField h (σ ^ 2 ^ (n + 1)) = 1 := by
      rw [← hN, ← hAσ]
      exact hφ
    exact (eq_one_of_psuConj_mul_psuField_eq_one N _ this).1
  have hσ : σ ^ 2 ^ n = 1 := s26U_sigma_pow h hp2 hmax hσ1
  obtain ⟨N', hN'⟩ := s26U_pow h A σ (2 ^ n)
  rw [hσ, map_one, mul_one] at hN'
  have hu : φ ^ 2 ^ n = psuConj h N' := by
    rw [hAσ]
    exact hN'
  have huu : φ ^ 2 ^ n * φ ^ 2 ^ n = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ']
    exact hφ
  have hsq : psuConj h (N' * N') * psuField h 1 = 1 := by
    rw [map_one, mul_one, map_mul, ← hu]
    exact huu
  obtain ⟨-, c₂, -, hc₂⟩ := eq_one_of_psuConj_mul_psuField_eq_one (N' * N') 1 hsq
  set M : Matrix (Fin 3) (Fin 3) K := ((N' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
  have hMM : M * M = (c₂ : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hc₂
    simpa [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul, ← Matrix.smul_one_eq_diagonal] using this
  have hQ00 : (M * M) 0 0 = (M * M) 2 2 := by
    rw [hMM]
    simp
  have hQ10 : (M * M) 1 0 = 0 := by
    rw [hMM]
    simp
  have hU : (M.map h.bar)ᵀ * M = 1 := N'.2
  have hfixk : ∀ k : ℕ, (φ ^ k) (unitaryProj h 3 r₀) = unitaryProj h 3 r₀ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, MulAut.mul_apply, hfix, ih]
  have hAr : psuConj h N' (unitaryProj h 3 r₀) = unitaryProj h 3 r₀ := by
    rw [← hu]
    exact hfixk _
  have hAx : psuConj h N' (unitaryProj h 3 (r₀ ^ 2 ^ n)) = unitaryProj h 3 (r₀ ^ 2 ^ n) := by
    rw [map_pow, map_pow, hAr]
  set Ninv : Matrix (Fin 3) (Fin 3) K :=
    ((((N' : GL (Fin 3) K))⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hNinv
  have hMN : M * Ninv = 1 := by rw [hM, hNinv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hNM : Ninv * M = 1 := by rw [hM, hNinv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hx : s26xM * M = M * s26xM := by
    obtain ⟨c, hcm⟩ := s26U_comm_of_conj_fix h N' (r₀ ^ 2 ^ n) hAx
    rw [← hM, hxr] at hcm
    have e : M * s26xM * Ninv = (c : K) • s26xM := by
      calc M * s26xM * Ninv = ((c : K) • (s26xM * M)) * Ninv := by rw [hcm]
        _ = (c : K) • (s26xM * (M * Ninv)) := by rw [Matrix.smul_mul, Matrix.mul_assoc]
        _ = (c : K) • s26xM := by rw [hMN, Matrix.mul_one]
    have htr : Matrix.trace (s26xM : Matrix (Fin 3) (Fin 3) K) =
        (c : K) * Matrix.trace (s26xM : Matrix (Fin 3) (Fin 3) K) := by
      calc Matrix.trace (s26xM : Matrix (Fin 3) (Fin 3) K)
          = Matrix.trace (Ninv * (M * s26xM)) := by
            rw [← Matrix.mul_assoc, hNM, Matrix.one_mul]
        _ = Matrix.trace ((M * s26xM) * Ninv) := Matrix.trace_mul_comm _ _
        _ = Matrix.trace ((c : K) • (s26xM : Matrix (Fin 3) (Fin 3) K)) := by rw [e]
        _ = (c : K) * Matrix.trace (s26xM : Matrix (Fin 3) (Fin 3) K) := by
            rw [Matrix.trace_smul, smul_eq_mul]
    have htr' : Matrix.trace (s26xM : Matrix (Fin 3) (Fin 3) K) = -1 := by
      simp [Matrix.trace, Fin.sum_univ_three, s26xM]
    rw [htr'] at htr
    have hc1 : (c : K) = 1 := by linear_combination htr
    rw [hc1, one_smul] at hcm
    exact hcm.symm
  obtain ⟨m02, m12, m20, m21⟩ := s26_block_diag h2 hx
  have hm22 : M 2 2 ≠ 0 := by
    intro h0
    have u22 := congrFun (congrFun hU 2) 2
    simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Fin.sum_univ_three, m02,
      m12, h0] at u22
  have hr : s26R0 a b c d * M = M * s26R0 a b c d := by
    obtain ⟨c', hc'⟩ := s26U_comm_of_conj_fix h N' r₀ hAr
    rw [← hM, hr₀m] at hc'
    have e22 := congrFun (congrFun hc' 2) 2
    simp [s26R0, Matrix.mul_apply, Fin.sum_univ_three, Matrix.smul_apply, Matrix.vecMul,
      dotProduct] at e22
    have hc1 : (c' : K) = 1 := by
      have : (1 - (c' : K)) * M 2 2 = 0 := by linear_combination e22
      have := (mul_eq_zero.mp this).resolve_right hm22
      linear_combination -this
    rw [hc1, one_smul] at hc'
    exact hc'.symm
  rcases s26_matrix_main_U h h2 ha hb hs₀ hs₀sq hs₀0 hnd hx hr hU hQ00 hQ10 with hM1 | hM1
  · left
    rw [hu]
    exact s26U_psuConj_scalar h N' (M 2 2) hM1
  · right
    rw [hu]
    exact s26U_psuConj_xN h N' hm22 (r₀ ^ 2 ^ n) hxr hxr2 hM1


include h in
theorem s26U_central_eq_one (hq : 2 < p ^ f) {z : unitarySU p f K 3}
    (hz : z ∈ Subgroup.center (unitarySU p f K 3))
    (h22 : ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1) : z = 1 := by
  rw [center_unitarySU_three (h := h) hq] at hz
  obtain ⟨c, -, -, hc⟩ := mem_unitaryScalars.mp hz
  have hcm : ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) (c : K) := by
    rw [hc]
    rfl
  have hc1 : (c : K) = 1 := by
    rw [hcm] at h22
    simpa using h22
  apply Subtype.ext
  apply Units.ext
  rw [hcm, hc1]
  simp

include h in
theorem s26_core_U [Finite K] (hodd : Odd (Nat.card K)) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hq1 : p ^ f % 4 = 1) {n : ℕ} (hmax : ¬ 2 ^ (n + 3) ∣ (p ^ f) ^ 2 - 1) (hn : 1 ≤ n)
    [Group.IsPerfect (unitarySU p f K 3)] {Y : Type} [Group Y] (ψ : unitarySU p f K 3 →* Y)
    (hker : ψ.ker ≤ Subgroup.center (unitarySU p f K 3)) (hsurj : Function.Surjective ψ)
    {r₀ : unitarySU p f K 3} {a b c d : K}
    (hr₀m : ((r₀ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = s26R0 a b c d)
    (hr1 : r₀ ^ 2 ^ (n + 1) = 1) (hr0 : r₀ ^ 2 ^ n ≠ 1) (β : MulAut Y) (hβr : β (ψ r₀) = ψ r₀)
    (hβ : β ^ 2 ^ (n + 1) = 1) :
    β ^ 2 ^ n = 1 ∨ β ^ 2 ^ n = MulAut.conj (ψ (r₀ ^ 2 ^ n)) := by
  have hq2 : 2 < p ^ f := by omega
  have hπk : (unitaryProj h 3).ker = Subgroup.center (unitarySU p f K 3) :=
    (ker_unitaryProj h 3).trans (center_unitarySU_three (h := h) hq2).symm
  have hk : ψ.ker ≤ (unitaryProj h 3).ker := by
    rw [hπk]
    exact hker
  obtain ⟨φ, hφ⟩ := s26_exists_isDescent hsurj hker (unitaryProj_surjective h 3) hπk β
  have h1 : φ (unitaryProj h 3 r₀) = unitaryProj h 3 r₀ := hφ _ _ hβr
  have hpow : ∀ k : ℕ, S26IsDescent ψ (unitaryProj h 3) (β ^ k) (φ ^ k) := fun k =>
    hφ.pow hsurj hk k
  have hφ2 : φ ^ 2 ^ (n + 1) = 1 := by
    have := hpow (2 ^ (n + 1))
    rw [hβ] at this
    ext x
    obtain ⟨s, rfl⟩ := unitaryProj_surjective h 3 x
    exact this s s (by simp)
  rcases s26_psu_main h hodd hp2 hq hq1 hmax hn φ hφ2 hr₀m hr1 hr0 h1 with h' | h'
  · left
    have := hpow (2 ^ n)
    rw [h'] at this
    exact s26_eq_one_of_isDescent_one hsurj hπk this
  · right
    have hd := hpow (2 ^ n)
    rw [h'] at hd
    have hd2 := (S26IsDescent.conj hk (r₀ ^ 2 ^ n)).inv.mul hsurj hd
    rw [inv_mul_cancel] at hd2
    have := s26_eq_one_of_isDescent_one hsurj hπk hd2
    exact (inv_mul_eq_one.mp this).symm


theorem s26_blockMat_three (A : Matrix (Fin 2) (Fin 2) K) :
    CFSG.ClassicalInvolution.Phan.blockMat 3 0 A =
      !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1] := by
  ext a b
  rw [CFSG.ClassicalInvolution.Phan.blockMat_apply]
  fin_cases a <;> fin_cases b <;> simp

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary in
theorem s26_aut164U (p : ℕ) [Fact p.Prime] : S26Aut164U p := by
  intro e hadm h4 Y _ ψ hker hsurj R hR s hs n hn hord hfac β hβs hβ
  have hf : 1 ≤ e := hadm.2.1
  have he : e ≠ 0 := by omega
  have hp2 : p ≠ 2 := by
    intro hp
    subst hp
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at h4
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have : 2 ^ (j + 1 + 1) = 4 * 2 ^ j := by ring
      rw [this] at h4
      omega
  have hq5 : 5 ≤ p ^ e := by
    have h2 : 2 ≤ p ^ e := by
      calc 2 ≤ p := (Fact.out : p.Prime).two_le
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ e := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hf
    omega
  have hodd : Odd (p ^ e) := Nat.odd_iff.mpr (by omega)
  have hF : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p e hf
  have hFp : Nat.card (GaloisField p (2 * e)) = p ^ (2 * e) := by
    rw [hF, ← pow_mul, mul_comm]
  let h : UnitaryFieldData p e (GaloisField p (2 * e)) := ⟨Fact.out, hf, hFp⟩
  have hoddK : Odd (Nat.card (GaloisField p (2 * e))) := by
    rw [hF, pow_two]
    exact hodd.mul hodd
  have : NeZero (2 * e) := ⟨by omega⟩
  have hnq : ((3 : ℕ), p ^ e) ≠ (3, 2) := by
    intro h'
    simp only [Prod.mk.injEq, true_and] at h'
    omega
  have hperf : Group.IsPerfect (unitarySU p e (GaloisField p (2 * e)) 3) :=
    (isQuasisimple_statedSU_of_card hF (le_refl 3) hnq).1.1
  obtain ⟨φ, hφ⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  let Φ₀ : Su (GaloisField p (2 * e)) p e 3 ≃* unitarySU p e (GaloisField p (2 * e)) 3 :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU hF 3)
  let Φ : (modelUniv .PSU 3 p e Fact.out).K ≃* unitarySU p e (GaloisField p (2 * e)) 3 :=
    φ.trans Φ₀
  let ψ₀ : unitarySU p e (GaloisField p (2 * e)) 3 →* Y := ψ.comp Φ.symm.toMonoidHom
  have hψ₀ : ∀ x, ψ₀ (Φ x) = ψ x := fun x => by
    show ψ (Φ.symm (Φ x)) = ψ x
    rw [MulEquiv.symm_apply_apply]
  have hsurj₀ : Function.Surjective ψ₀ := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨Φ x, by rw [hψ₀, hx]⟩
  have hker₀ : ψ₀.ker ≤ Subgroup.center (unitarySU p e (GaloisField p (2 * e)) 3) := by
    intro z hz
    obtain ⟨x, rfl⟩ := Φ.surjective z
    have hx : x ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, ← hψ₀]
      exact hz
    have hxc := hker hx
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := Φ.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hxc y']
  have hRl := (hφ R).mp hR
  obtain ⟨g, hg⟩ := (mem_longRootSetU_iff (show 2 ≤ 3 by norm_num)).mp hRl
  have hs' : φ s ∈ R.map φ.toMonoidHom := ⟨s, hs, rfl⟩
  rw [hg] at hs'
  obtain ⟨r, hr, hgr⟩ := hs'
  obtain ⟨A₀, rfl⟩ := hr
  let g₁ : unitarySU p e (GaloisField p (2 * e)) 3 := Φ₀ g
  let r₀ : unitarySU p e (GaloisField p (2 * e)) 3 := Φ₀ (blockEmb _ p e 3 2 0 (by omega) A₀)
  have hΦs : Φ s = g₁ * r₀ * g₁⁻¹ := by
    have h1 : g * blockEmb _ p e 3 2 0 (by omega) A₀ * g⁻¹ = φ s := hgr
    show Φ₀ (φ s) = _
    rw [← h1, map_mul, map_mul, map_inv]
  let ψ₁ : unitarySU p e (GaloisField p (2 * e)) 3 →* Y := ψ₀.comp (MulAut.conj g₁).toMonoidHom
  have hψ₁ : ∀ x, ψ₁ x = ψ₀ (g₁ * x * g₁⁻¹) := fun x => rfl
  have hψ₁r : ψ₁ r₀ = ψ s := by
    rw [hψ₁, ← hΦs, hψ₀]
  have hsurj₁ : Function.Surjective ψ₁ := by
    intro y
    obtain ⟨x, hx⟩ := hsurj₀ y
    refine ⟨g₁⁻¹ * x * g₁, ?_⟩
    have hx' : g₁ * (g₁⁻¹ * x * g₁) * g₁⁻¹ = x := by group
    rw [hψ₁, hx']
    exact hx
  have hker₁ : ψ₁.ker ≤ Subgroup.center (unitarySU p e (GaloisField p (2 * e)) 3) := by
    intro x hx
    rw [MonoidHom.mem_ker, hψ₁] at hx
    exact s26_center_of_conj g₁ x (hker₀ hx)
  have hr₀m : ((r₀ : GL (Fin 3) (GaloisField p (2 * e))) :
      Matrix (Fin 3) (Fin 3) (GaloisField p (2 * e))) =
      s26R0 ((suMat A₀) 0 0) ((suMat A₀) 0 1) ((suMat A₀) 1 0) ((suMat A₀) 1 1) := by
    show suMat (blockEmb _ p e 3 2 0 (by omega) A₀) = _
    rw [suMat_blockEmb, s26_blockMat_three]
    rfl
  have hpow22 : ∀ k : ℕ, (((r₀ ^ k : unitarySU p e (GaloisField p (2 * e)) 3) :
      GL (Fin 3) (GaloisField p (2 * e))) :
      Matrix (Fin 3) (Fin 3) (GaloisField p (2 * e))) 2 2 = 1 := by
    intro k
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hr₀m, s26R0_eq_blk, ← s26Blk_pow]
    simp [s26Blk]
  have hq2 : 2 < p ^ e := by omega
  have hr1 : r₀ ^ 2 ^ (n + 1) = 1 := by
    have h1 : (ψ₁ r₀) ^ 2 ^ (n + 1) = 1 := by
      rw [hψ₁r, ← hord]
      exact pow_orderOf_eq_one _
    rw [← map_pow, ← MonoidHom.mem_ker] at h1
    exact s26U_central_eq_one h hq2 (hker₁ h1) (hpow22 _)
  have hr0 : r₀ ^ 2 ^ n ≠ 1 := by
    intro h0
    have h1 : (ψ₁ r₀) ^ 2 ^ n = 1 := by rw [← map_pow, h0, map_one]
    have h3 : 2 ^ n < orderOf (ψ₁ r₀) := by
      rw [hψ₁r, hord]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    exact pow_ne_one_of_lt_orderOf (pow_ne_zero n (by norm_num)) h3 h1
  have hmax : ¬ 2 ^ (n + 3) ∣ (p ^ e) ^ 2 - 1 := by
    intro hdvd
    have hcardSL : Nat.card SL(2, GaloisField p e) = p ^ e * ((p ^ e) ^ 2 - 1) := by
      rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, GaloisField.card p e he]
    have hdvd' : 2 ^ (n + 3) ∣ Nat.card SL(2, GaloisField p e) := by
      rw [hcardSL]
      exact Dvd.dvd.mul_left hdvd _
    have hpos : Nat.card SL(2, GaloisField p e) ≠ 0 := Nat.card_pos.ne'
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).mp hdvd'
    omega
  have hβ₁ : β (ψ₁ r₀) = ψ₁ r₀ := by
    rw [hψ₁r]
    exact hβs
  have hcore := s26_core_U h hoddK hp2 hq5 h4 hmax hn ψ₁ hker₁ hsurj₁ hr₀m hr1 hr0 β hβ₁ hβ
  have hx : ψ₁ (r₀ ^ 2 ^ n) = ψ s ^ 2 ^ n := by
    rw [map_pow, hψ₁r]
  rcases hcore with h' | h'
  · exact Or.inl h'
  · right
    rw [h', hx]

end CFSG.ClassicalInvolution.Asc77
