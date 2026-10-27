module

public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Basic

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open Matrix CFSG.Open CFSG.Assembly.LowTwoRank CFSG.SectionRank.ClassicalEven

section Two

variable {K : Type} [Field K]

theorem su2_cube_exists (h2 : (2 : K) = 0) (φ : K →+* K) (hφφ : ∀ x, φ (φ x) = x)
    (hcube : ∀ x : K, x ^ 3 = 1 → φ x = x) (a : K) (ha : φ a * a = 1) (ha1 : a ≠ 1) :
    ∃ M : Matrix (Fin 2) (Fin 2) K, (M.map φ)ᵀ * M = 1 ∧ M ^ 3 = 1 ∧ M.det = 1 ∧ M 0 1 ≠ 0 := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have h1a : 1 + a ≠ 0 := fun h => ha1 (by linear_combination h - h2)
  obtain ⟨s, hs⟩ : ∃ s : K, s * (1 + a) = 1 := ⟨(1 + a)⁻¹, inv_mul_cancel₀ h1a⟩
  have hφs : φ s * (1 + φ a) = 1 := by
    have := congrArg φ hs
    simpa [map_mul, map_add] using this
  let Q : Matrix (Fin 2) (Fin 2) K := !![1, s; 1, s * a]
  let J : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]
  let M0 : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 1]
  let Qd : Matrix (Fin 2) (Fin 2) K := (Q.map φ)ᵀ
  have hJJ : J * J = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply, Fin.sum_univ_two]
  have hQ : Qd * Q = J := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Qd, Q, J, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply]
    · linear_combination h2
    · linear_combination hs
    · linear_combination hφs
    · linear_combination (φ s * s) * h2 + (φ s * s) * ha
  have hM0J : M0ᵀ * J * M0 = J := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [M0, J, Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination h2
  have hM03 : M0 ^ 3 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [M0, pow_succ, Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination h2
  have hdet0 : M0.det = 1 := by
    simp [M0, Matrix.det_fin_two]; linear_combination (-1 : K) * h2
  have hM0s : M0ᵀ = M0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [M0]
  have hJQ : J * Qd * Q = 1 := by rw [mul_assoc, hQ, hJJ]
  have hQJ : Q * (J * Qd) = 1 := mul_eq_one_comm.mp hJQ
  let M : Matrix (Fin 2) (Fin 2) K := Q * M0 * (J * Qd)
  have hpow : ∀ k : ℕ, M ^ k = Q * M0 ^ k * (J * Qd) := by
    intro k
    induction k with
    | zero => simp [hQJ]
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      calc Q * M0 ^ k * (J * Qd) * (Q * M0 * (J * Qd))
          = Q * M0 ^ k * (J * Qd * Q) * M0 * (J * Qd) := by simp only [Matrix.mul_assoc]
        _ = Q * (M0 ^ k * M0) * (J * Qd) := by rw [hJQ]; simp only [Matrix.mul_assoc, Matrix.mul_one]
  have hmapJ : J.map φ = J := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [J]
  have hmapM0 : M0.map φ = M0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [M0]
  have hQQ : (Q.map φ).map φ = Q := by
    ext i j; simp [Matrix.map_apply, hφφ]
  have hQd : ((Q.map φ)ᵀ.map φ)ᵀ = Q := by
    ext i j; simp [Matrix.map_apply, Matrix.transpose_apply, hφφ]
  have hJt : Jᵀ = J := by ext i j; fin_cases i <;> fin_cases j <;> simp [J]
  have hd1 : ((J * Qd).map φ)ᵀ = Q * J := by
    rw [Matrix.map_mul, Matrix.transpose_mul, hmapJ, hJt]
    simp only [Qd, hQd]
  have hM0J' : M0 * J * M0 = J := by
    have := hM0J
    rwa [hM0s] at this
  have hdet : M.det = 1 := by
    have h1 : Q.det * (J * Qd).det = 1 := by rw [← Matrix.det_mul, hQJ, Matrix.det_one]
    show (Q * M0 * (J * Qd)).det = 1
    rw [Matrix.det_mul (Q * M0) (J * Qd), Matrix.det_mul Q M0]
    calc Q.det * M0.det * (J * Qd).det = M0.det * (Q.det * (J * Qd).det) := by ring
      _ = 1 := by rw [h1, hdet0, mul_one]
  have hnc : (M.map φ)ᵀ = Q * J * (M0 * Qd) := by
    have hm1 : (Q * M0 * (J * Qd)).map φ = (Q * M0).map φ * (J * Qd).map φ := Matrix.map_mul
    have hm2 : (Q * M0).map φ = Q.map φ * M0.map φ := Matrix.map_mul
    show ((Q * M0 * (J * Qd)).map φ)ᵀ = _
    rw [hm1, Matrix.transpose_mul, hd1, hm2, Matrix.transpose_mul, hmapM0, hM0s]
  refine ⟨M, ?_, ?_, hdet, ?_⟩
  · rw [hnc]
    show Q * J * (M0 * Qd) * (Q * M0 * (J * Qd)) = 1
    calc Q * J * (M0 * Qd) * (Q * M0 * (J * Qd))
        = Q * J * M0 * (Qd * Q) * M0 * (J * Qd) := by simp only [Matrix.mul_assoc]
      _ = Q * (J * (M0 * J * M0) * J) * Qd := by rw [hQ]; simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hM0J', hJJ, Matrix.one_mul, Matrix.mul_assoc]
        exact hQJ
  · rw [hpow, hM03, Matrix.mul_one, hQJ]
  · have hQd_eq : Qd = !![1, 1; φ s, φ s * φ a] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Qd, Q, Matrix.map_apply]
    have hent : M 0 1 = 1 + s + s * (φ s * φ a) := by
      show (Q * M0 * (J * Qd)) 0 1 = _
      rw [hQd_eq]
      simp [Q, M0, J, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
      ring
    rw [hent]
    have hφa : φ a = a⁻¹ := eq_inv_of_mul_eq_one_left ha
    have hs1 : φ s * (1 + a) = a := by
      have : φ s * (1 + φ a) * a = a := by rw [hφs, one_mul]
      calc φ s * (1 + a) = φ s * (1 + φ a) * a := by
            rw [mul_assoc, add_mul, one_mul, ha]; ring
        _ = a := this
    have hs2 : φ s = a * s := by
      have : (φ s - a * s) * (1 + a) = 0 := by linear_combination hs1 - a * hs
      rcases mul_eq_zero.1 this with h | h
      · exact sub_eq_zero.1 h
      · exact absurd h h1a
    have hprod : φ s * φ a = s := by
      rw [hs2, hφa]; field_simp
    rw [hprod]
    intro h0
    have hs3 : s ^ 3 = 1 := by
      have : s ^ 3 - 1 = (s - 1) * (1 + s + s * s) := by ring
      have h' : s ^ 3 - 1 = 0 := by rw [this, h0, mul_zero]
      exact sub_eq_zero.1 h'
    have := hcube s hs3
    rw [hs2] at this
    have hs0 : s ≠ 0 := by rintro rfl; simp at hs
    exact ha1 (by
      have h' : s * (a - 1) = 0 := by linear_combination this
      rcases mul_eq_zero.1 h' with h | h
      · exact absurd h hs0
      · exact sub_eq_zero.1 h)

end Two

section Block
variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def pairIncl (e : Fin 3 → Fin 2 → ι) (b : Fin 3) : Matrix ι (Fin 2) K :=
  Matrix.of fun i k => if i = e b k then 1 else 0

@[expose] def blk (e : Fin 3 → Fin 2 → ι) (b : Fin 3) (M : Matrix (Fin 2) (Fin 2) K) : Matrix ι ι K :=
  1 + (pairIncl e b : Matrix ι (Fin 2) K) * (M - 1) * (pairIncl e b : Matrix ι (Fin 2) K)ᵀ

variable {e : Fin 3 → Fin 2 → ι}

theorem pairIncl_transpose_mul
    (he : ∀ b k c l, e b k = e c l → b = c ∧ k = l) (b c : Fin 3) :
    (pairIncl e b : Matrix ι (Fin 2) K)ᵀ * (pairIncl e c : Matrix ι (Fin 2) K) =
      (if b = c then 1 else 0 : Matrix (Fin 2) (Fin 2) K) := by
  ext k l
  simp only [Matrix.mul_apply, pairIncl, Matrix.transpose_apply, Matrix.of_apply, ite_mul, one_mul,
    zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (e b k)]
  simp only [Finset.mem_univ, ite_true]
  by_cases hbc : b = c <;> by_cases hkl : k = l
  · subst hbc; subst hkl; simp
  · subst hbc; have : ¬ (e b k = e b l) := fun h => hkl (he _ _ _ _ h).2
    simp [this, hkl]
  · have : ¬ (e b k = e c l) := fun h => hbc (he _ _ _ _ h).1
    simp [this, hbc]
  · have : ¬ (e b k = e c l) := fun h => hbc (he _ _ _ _ h).1
    simp [this, hbc]

theorem pairIncl_transpose_mul_self (he : ∀ b k c l, e b k = e c l → b = c ∧ k = l) (b : Fin 3) :
    (pairIncl e b : Matrix ι (Fin 2) K)ᵀ * (pairIncl e b : Matrix ι (Fin 2) K) = 1 := by
  rw [pairIncl_transpose_mul he]; simp

theorem pairIncl_transpose_mul_ne (he : ∀ b k c l, e b k = e c l → b = c ∧ k = l) {b c : Fin 3}
    (h : b ≠ c) :
    (pairIncl e b : Matrix ι (Fin 2) K)ᵀ * (pairIncl e c : Matrix ι (Fin 2) K) = 0 := by
  rw [pairIncl_transpose_mul he]; simp [h]

omit [Fintype ι] in
theorem blk_one (b : Fin 3) : blk e b (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by simp [blk]

theorem blk_mul (he : ∀ b k c l, e b k = e c l → b = c ∧ k = l) (b : Fin 3)
    (M N : Matrix (Fin 2) (Fin 2) K) : blk e b M * blk e b N = blk e b (M * N) := by
  set P : Matrix ι (Fin 2) K := pairIncl e b with hPdef
  have hP : Pᵀ * P = 1 := pairIncl_transpose_mul_self he b
  have h : P * (M - 1) * Pᵀ * (P * (N - 1) * Pᵀ) = P * ((M - 1) * (N - 1)) * Pᵀ := by
    calc P * (M - 1) * Pᵀ * (P * (N - 1) * Pᵀ)
        = P * (M - 1) * (Pᵀ * P) * (N - 1) * Pᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP]; simp only [Matrix.mul_assoc, Matrix.mul_one]
  have hMN : M * N - 1 = (M - 1) + (N - 1) + (M - 1) * (N - 1) := by noncomm_ring
  unfold blk
  rw [← hPdef, hMN]
  have e1 : ∀ X Y : Matrix ι ι K, (1 + X) * (1 + Y) = 1 + X + Y + X * Y := fun X Y => by
    noncomm_ring
  rw [e1, h]
  simp only [Matrix.mul_add, Matrix.add_mul]
  abel


theorem blk_pow (he : ∀ b k c l, e b k = e c l → b = c ∧ k = l) (b : Fin 3)
    (M : Matrix (Fin 2) (Fin 2) K) (k : ℕ) : blk e b M ^ k = blk e b (M ^ k) := by
  induction k with
  | zero => simp [blk_one]
  | succ k ih => rw [pow_succ, ih, blk_mul he, pow_succ]

theorem blk_det (he : ∀ b k c l, e b k = e c l → b = c ∧ k = l) (b : Fin 3)
    (M : Matrix (Fin 2) (Fin 2) K) : (blk e b M).det = M.det := by
  set P : Matrix ι (Fin 2) K := pairIncl e b with hPdef
  have hP : Pᵀ * P = 1 := pairIncl_transpose_mul_self he b
  have : blk e b M = 1 + (P * (M - 1)) * Pᵀ := rfl
  rw [this, Matrix.det_one_add_mul_comm]
  have h2 : Pᵀ * (P * (M - 1)) = M - 1 := by rw [← Matrix.mul_assoc, hP, Matrix.one_mul]
  rw [h2]; simp

theorem blk_comm (he : ∀ b k c l, e b k = e c l → b = c ∧ k = l) {b c : Fin 3} (h : b ≠ c)
    (M N : Matrix (Fin 2) (Fin 2) K) : blk e b M * blk e c N = blk e c N * blk e b M := by
  set P : Matrix ι (Fin 2) K := pairIncl e b with hPdef
  set Q : Matrix ι (Fin 2) K := pairIncl e c with hQdef
  have h1 : Pᵀ * Q = 0 := pairIncl_transpose_mul_ne he h
  have h2 : Qᵀ * P = 0 := pairIncl_transpose_mul_ne he h.symm
  have e1 : ∀ X Y : Matrix ι ι K, (1 + X) * (1 + Y) = 1 + X + Y + X * Y := fun X Y => by
    noncomm_ring
  unfold blk
  rw [← hPdef, ← hQdef, e1, e1]
  have h3 : P * (M - 1) * Pᵀ * (Q * (N - 1) * Qᵀ) = 0 := by
    calc _ = P * (M - 1) * (Pᵀ * Q) * (N - 1) * Qᵀ := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h1]; simp
  have h4 : Q * (N - 1) * Qᵀ * (P * (M - 1) * Pᵀ) = 0 := by
    calc _ = Q * (N - 1) * (Qᵀ * P) * (M - 1) * Pᵀ := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h2]; simp
  rw [h3, h4]
  abel


omit [Fintype ι] in
theorem pairIncl_map (φ : K →+* K) (b : Fin 3) :
    (pairIncl e b : Matrix ι (Fin 2) K).map φ = pairIncl e b := by
  ext i k; simp only [pairIncl, Matrix.map_apply, Matrix.of_apply]; split_ifs <;> simp

theorem blk_map_transpose (φ : K →+* K) (b : Fin 3) (M : Matrix (Fin 2) (Fin 2) K) :
    ((blk e b M).map φ)ᵀ = blk e b ((M.map φ)ᵀ) := by
  unfold blk
  have h1 : ((1 : Matrix ι ι K).map φ) = 1 := Matrix.map_one φ (map_zero φ) (map_one φ)
  have h2 : ((1 : Matrix (Fin 2) (Fin 2) K).map φ) = 1 := Matrix.map_one φ (map_zero φ) (map_one φ)
  have h3 : ((M - 1).map φ) = M.map φ - 1 := by rw [Matrix.map_sub _ (map_sub φ), h2]
  have hm1 : ∀ (A : Matrix ι (Fin 2) K) (B : Matrix (Fin 2) (Fin 2) K) (C : Matrix (Fin 2) ι K),
      (A * B * C).map φ = A.map φ * B.map φ * C.map φ := fun A B C => by
    rw [Matrix.map_mul, Matrix.map_mul]
  have hPt : (pairIncl e b : Matrix ι (Fin 2) K)ᵀ.map φ = (pairIncl e b)ᵀ := by
    rw [Matrix.transpose_map, pairIncl_map]
  rw [Matrix.map_add _ (map_add φ), h1, hm1, h3, hPt, pairIncl_map, Matrix.transpose_add,
    Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_sub, Matrix.transpose_one]
  simp only [Matrix.mul_assoc]


theorem blk_apply_same (he : ∀ b k c l, e b k = e c l → b = c ∧ k = l) (b : Fin 3)
    (M : Matrix (Fin 2) (Fin 2) K) (k l : Fin 2) : blk e b M (e b k) (e b l) = M k l := by
  have h01 : e b 0 ≠ e b 1 := fun h => by simpa using (he _ _ _ _ h).2
  have h10 : e b 1 ≠ e b 0 := h01.symm
  fin_cases k <;> fin_cases l <;>
    simp [blk, Matrix.mul_apply, Fin.sum_univ_two, pairIncl, Matrix.one_apply, h01, h10]

theorem blk_apply_other (he : ∀ b k c l, e b k = e c l → b = c ∧ k = l) {b c : Fin 3} (h : c ≠ b)
    (M : Matrix (Fin 2) (Fin 2) K) (k : Fin 2) (j : ι) :
    blk e b M (e c k) j = (1 : Matrix ι ι K) (e c k) j := by
  have h0 : e c k ≠ e b 0 := fun h' => h (he _ _ _ _ h').1
  have h1 : e c k ≠ e b 1 := fun h' => h (he _ _ _ _ h').1
  simp [blk, Matrix.mul_apply, Fin.sum_univ_two, pairIncl, h0, h1]

theorem mul_apply_of_row {A B : Matrix ι ι K} {i : ι} (h : ∀ j, A i j = (1 : Matrix ι ι K) i j)
    (j : ι) : (A * B) i j = B i j := by
  simp [Matrix.mul_apply, h, Matrix.one_apply]


@[expose] def blkGL (he : ∀ b k c l, e b k = e c l → b = c ∧ k = l) (b : Fin 3)
    (M : Matrix (Fin 2) (Fin 2) K) (h3 : M ^ 3 = 1) : GL ι K :=
  ⟨blk e b M, blk e b (M * M), by rw [blk_mul he, ← pow_three, h3, blk_one],
    by rw [blk_mul he, ← pow_three', h3, blk_one]⟩

theorem coe_blkGL (he : ∀ b k c l, e b k = e c l → b = c ∧ k = l) (b : Fin 3)
    (M : Matrix (Fin 2) (Fin 2) K) (h3 : M ^ 3 = 1) :
    ((blkGL he b M h3 : GL ι K) : Matrix ι ι K) = blk e b M := rfl

theorem blkGL_pow_three (he : ∀ b k c l, e b k = e c l → b = c ∧ k = l) (b : Fin 3)
    (M : Matrix (Fin 2) (Fin 2) K) (h3 : M ^ 3 = 1) : blkGL he b M h3 ^ 3 = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, coe_blkGL, blk_pow he, h3, blk_one]; rfl

theorem blkGL_commute (he : ∀ b k c l, e b k = e c l → b = c ∧ k = l) {b c : Fin 3} (h : b ≠ c)
    (M : Matrix (Fin 2) (Fin 2) K) (h3 : M ^ 3 = 1) :
    Commute (blkGL he b M h3 : GL ι K) (blkGL he c M h3) :=
  Units.ext (by
    simp only [Units.val_mul, coe_blkGL]; exact blk_comm he h M M)

theorem scalar_apply_ne {u : Kˣ} {i j : ι} (h : i ≠ j) :
    ((Matrix.GeneralLinearGroup.scalar ι u : GL ι K) : Matrix ι ι K) i j = 0 := by
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply, h]

end Block

section Final

variable {K : Type} [Field K]

theorem psu_three_le_pRank_of_one_mod_three [Finite K] [CharP K 2] {n e : ℕ}
    (hK : Nat.card K = (2 ^ e) ^ 2) (h3 : 3 ∣ 2 ^ e - 1) (hn : 6 ≤ n) :
    3 ≤ pRank 3 (⊤ : Subgroup (StatedProj (StatedSU n (2 ^ e) K))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : ExpChar K 2 := ExpChar.prime Nat.prime_two
  have hq1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  set q : ℕ := 2 ^ e with hq
  have hcardK : Fintype.card K = q ^ 2 := by rw [← Nat.card_eq_fintype_card, hK]
  let φ : K →+* K := iterateFrobenius K 2 e
  have hφ : ∀ x, φ x = x ^ q := fun x => rfl
  have hφφ : ∀ x, φ (φ x) = x := fun x => by
    rw [hφ, hφ, ← pow_mul, ← sq, ← hcardK, FiniteField.pow_card]
  have hcube : ∀ x : K, x ^ 3 = 1 → φ x = x := fun x hx => by
    rw [hφ]
    obtain ⟨m, hm⟩ := h3
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    calc x ^ q = x ^ (q - 1) * x := by rw [← pow_succ, Nat.sub_add_cancel hq1]
      _ = x := by rw [hm, mul_comm, pow_mul, hx, one_pow, mul_one]
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hcardU : Nat.card Kˣ = (q + 1) * (q - 1) := by
    rw [Nat.card_units, hK, ← Nat.sq_sub_sq, one_pow]
  have hp : (q + 1).minFac.Prime := Nat.minFac_prime (by omega)
  have := Fact.mk hp
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) (q + 1).minFac
    (by rw [hcardU]; exact (Nat.minFac_dvd _).mul_right _)
  have haq : a ^ (q + 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (by rw [ha]; exact Nat.minFac_dvd _)
  have ha1 : (a : K) ≠ 1 := fun h => by
    have : a = 1 := Units.ext h
    rw [this, orderOf_one] at ha
    exact hp.one_lt.ne ha
  have haφ : φ (a : K) * a = 1 := by
    rw [hφ, ← pow_succ]
    have := congrArg (fun u : Kˣ => (u : K)) haq
    simpa using this
  obtain ⟨M, hM1, hM3, hMdet, hM01⟩ := su2_cube_exists h2 φ hφφ hcube (a : K) haφ ha1
  let c : Fin 3 → Fin 2 → Fin n := fun b k => ⟨2 * b.val + k.val, by omega⟩
  have hc : ∀ b k b' k', c b k = c b' k' → b = b' ∧ k = k' := fun b k b' k' h => by
    have := congrArg Fin.val h
    simp only [c] at this
    have hb := b.isLt; have hk := k.isLt; have hb' := b'.isLt; have hk' := k'.isLt
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  have hunit : ∀ b : Fin 3, blkGL hc b M hM3 ∈ StatedSU n q K := fun b => by
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · show (blk c b M).det = 1
      rw [blk_det hc, hMdet]
    · show ((blk c b M).map (· ^ q))ᵀ * blk c b M = 1
      have : (fun x : K => x ^ q) = ⇑φ := funext fun x => (hφ x).symm
      rw [this, blk_map_transpose, blk_mul hc, hM1, blk_one]
  have hne : ∀ b k l, k ≠ l → c b k ≠ c b l := fun b k l h h' => h (hc _ _ _ _ h').2
  refine three_le_pRank_statedProj (hunit 0) (hunit 1) (hunit 2) (blkGL_pow_three hc _ _ _)
    (blkGL_pow_three hc _ _ _) (blkGL_pow_three hc _ _ _)
    (blkGL_commute hc (by decide) M hM3) (blkGL_commute hc (by decide) M hM3)
    (blkGL_commute hc (by decide) M hM3) ?_ ?_ ?_
  · rintro ⟨u, hu⟩
    have h1 := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) (c 0 0) (c 0 1)) hu
    simp only [coe_blkGL, blk_apply_same hc] at h1
    rw [scalar_apply_ne (hne 0 0 1 (by decide))] at h1
    exact hM01 h1.symm
  · rintro m _ ⟨u, rfl⟩ h
    have h1 := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) (c 1 0) (c 1 1)) h
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, coe_blkGL, blk_pow hc] at h1
    rw [mul_apply_of_row (fun j => blk_apply_other hc (by decide) _ _ _),
      scalar_apply_ne (hne 1 0 1 (by decide)), blk_apply_same hc] at h1
    exact hM01 h1.symm
  · rintro m k _ ⟨u, rfl⟩ h
    have h1 := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) (c 2 0) (c 2 1)) h
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, coe_blkGL, blk_pow hc] at h1
    rw [mul_apply_of_row (fun j => by
        rw [mul_apply_of_row (fun j' => blk_apply_other hc (by decide) _ _ _),
          blk_apply_other hc (by decide)]),
      scalar_apply_ne (hne 2 0 1 (by decide)), blk_apply_same hc] at h1
    exact hM01 h1.symm

end Final

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
