module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.Generic.BProg.B2.WeakSigDiag
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix

namespace GenLocU4ExtBd

variable {K : Type} [Field K]

@[expose] def bd (B B' : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  !![B 0 0, B 0 1, 0, 0; B 1 0, B 1 1, 0, 0; 0, 0, B' 0 0, B' 0 1; 0, 0, B' 1 0, B' 1 1]

theorem bd_mul (B B' C C' : Matrix (Fin 2) (Fin 2) K) : bd B B' * bd C C' = bd (B * C) (B' * C') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem bd_one : bd (1 : Matrix (Fin 2) (Fin 2) K) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd]

theorem bd_smul (μ : K) (B B' : Matrix (Fin 2) (Fin 2) K) : μ • bd B B' = bd (μ • B) (μ • B') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd]

theorem bd_neg (B B' : Matrix (Fin 2) (Fin 2) K) : -bd B B' = bd (-B) (-B') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd]

theorem bd_inj {B B' C C' : Matrix (Fin 2) (Fin 2) K} (h : bd B B' = bd C C') : B = C ∧ B' = C' := by
  constructor
  · ext i j
    have := congrFun (congrFun h i.castSucc.castSucc) j.castSucc.castSucc
    fin_cases i <;> fin_cases j <;> simpa [bd] using this
  · ext i j
    have := congrFun (congrFun h i.succ.succ) j.succ.succ
    fin_cases i <;> fin_cases j <;> simpa [bd] using this

theorem bd_unitary {q : ℕ} (hq : q ≠ 0) (B B' : Matrix (Fin 2) (Fin 2) K) :
    ((bd B B').map (· ^ q))ᵀ * bd B B' = bd ((B.map (· ^ q))ᵀ * B) ((B'.map (· ^ q))ᵀ * B') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bd, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, zero_pow hq]

theorem diag_eq_bd : Matrix.diagonal ![-1, -1, 1, 1] = bd (-1 : Matrix (Fin 2) (Fin 2) K) 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd, Matrix.diagonal]

theorem exists_bd_of_comm (h2 : (2 : K) ≠ 0) (y : Matrix (Fin 4) (Fin 4) K)
    (hD : y * Matrix.diagonal ![-1, -1, 1, 1] = Matrix.diagonal ![-1, -1, 1, 1] * y) :
    ∃ B B' : Matrix (Fin 2) (Fin 2) K, y = bd B B' := by
  have key : ∀ (i j : Fin 4), y i j * (![-1, -1, 1, 1] : Fin 4 → K) j = (![-1, -1, 1, 1] : Fin 4 → K) i * y i j := by
    intro i j
    have := congrFun (congrFun hD i) j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  have half : ∀ x : K, x * (-1) = 1 * x → x = 0 := fun x hx => by
    have : (2 : K) * x = 0 := by linear_combination -hx
    exact (mul_eq_zero.1 this).resolve_left h2
  have half' : ∀ x : K, x * 1 = (-1) * x → x = 0 := fun x hx => by
    have : (2 : K) * x = 0 := by linear_combination hx
    exact (mul_eq_zero.1 this).resolve_left h2
  have z02 : y 0 2 = 0 := half' _ (by simpa using key 0 2)
  have z03 : y 0 3 = 0 := half' _ (by simpa using key 0 3)
  have z12 : y 1 2 = 0 := half' _ (by simpa using key 1 2)
  have z13 : y 1 3 = 0 := half' _ (by simpa using key 1 3)
  have z20 : y 2 0 = 0 := half _ (by simpa using key 2 0)
  have z21 : y 2 1 = 0 := half _ (by simpa using key 2 1)
  have z30 : y 3 0 = 0 := half _ (by simpa using key 3 0)
  have z31 : y 3 1 = 0 := half _ (by simpa using key 3 1)
  refine ⟨!![y 0 0, y 0 1; y 1 0, y 1 1], !![y 2 2, y 2 3; y 3 2, y 3 3], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd, z02, z03, z12, z13, z20, z21, z30, z31]

theorem pow_eq_self_of_sq_neg_one {q : ℕ} (hq : q % 4 = 1) {a : K} (ha : a * a = -1) : a ^ q = a := by
  obtain ⟨k, hk⟩ : ∃ k, q = 4 * k + 1 := ⟨q / 4, by omega⟩
  have h4 : a ^ 4 = 1 := by
    have : a ^ 4 = (a * a) * (a * a) := by ring
    rw [this, ha]; norm_num
  rw [hk, pow_succ, pow_mul, h4, one_pow, one_mul]

theorem tr_zero {q : ℕ} (hq : q % 4 = 1) (h2 : (2 : K) ≠ 0)
    (B : Matrix (Fin 2) (Fin 2) K) (hsq : B * B = -1) (hU : (B.map (· ^ q))ᵀ * B = 1) :
    B 1 1 = - B 0 0 := by
  have e00 := congrFun (congrFun hsq 0) 0
  have e01 := congrFun (congrFun hsq 0) 1
  have e10 := congrFun (congrFun hsq 1) 0
  have e11 := congrFun (congrFun hsq 1) 1
  have u00 := congrFun (congrFun hU 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11 u00
  by_contra hs
  have hs' : B 0 0 + B 1 1 ≠ 0 := fun h => hs (by linear_combination h)
  have hb : B 0 1 = 0 := by
    have : B 0 1 * (B 0 0 + B 1 1) = 0 := by linear_combination e01
    exact (mul_eq_zero.1 this).resolve_right hs'
  have hc : B 1 0 = 0 := by
    have : B 1 0 * (B 0 0 + B 1 1) = 0 := by linear_combination e10
    exact (mul_eq_zero.1 this).resolve_right hs'
  rw [hb] at e00 e11
  rw [hc] at e00 e11 u00
  have hadd : (B 0 0 - B 1 1) * (B 0 0 + B 1 1) = 0 := by linear_combination e00 - e11
  have had : B 0 0 = B 1 1 := by
    have := (mul_eq_zero.1 hadd).resolve_right hs'
    linear_combination this
  have ha2 : B 0 0 * B 0 0 = -1 := by linear_combination e00
  have hpow := pow_eq_self_of_sq_neg_one hq ha2
  rw [hpow] at u00
  apply h2
  linear_combination ha2 - u00

theorem commutant_two (h2 : (2 : K) ≠ 0) (a b e : K) (hab : a * a + b * e = -1)
    (C : Matrix (Fin 2) (Fin 2) K) (hCB : C * !![a, b; e, -a] = !![a, b; e, -a] * C) :
    ∃ t d : K, C = t • (1 : Matrix (Fin 2) (Fin 2) K) + d • !![a, b; e, -a] := by
  have e00 := congrFun (congrFun hCB 0) 0
  have e01 := congrFun (congrFun hCB 0) 1
  have e10 := congrFun (congrFun hCB 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  have h1 : C 0 1 * e = b * C 1 0 := by linear_combination e00
  have h2' : b * (C 0 0 - C 1 1) = 2 * a * C 0 1 := by linear_combination e01
  have h3 : e * (C 0 0 - C 1 1) = 2 * a * C 1 0 := by linear_combination -e10
  have key : ∃ d : K, C 0 0 - C 1 1 = 2 * d * a ∧ C 0 1 = d * b ∧ C 1 0 = d * e := by
    by_cases hb : b = 0
    · by_cases he : e = 0
      · have ha : a ≠ 0 := by
          intro ha0
          rw [ha0, hb, he] at hab
          exact one_ne_zero (by linear_combination hab)
        refine ⟨(C 0 0 - C 1 1) / (2 * a), ?_, ?_, ?_⟩
        · field_simp
        · rw [hb]
          have : 2 * a * C 0 1 = 0 := by rw [← h2', hb]; ring
          have := (mul_eq_zero.1 this).resolve_left (mul_ne_zero h2 ha)
          simp [this]
        · rw [he]
          have : 2 * a * C 1 0 = 0 := by rw [← h3, he]; ring
          have := (mul_eq_zero.1 this).resolve_left (mul_ne_zero h2 ha)
          simp [this]
      · refine ⟨C 1 0 / e, ?_, ?_, ?_⟩
        · field_simp
          linear_combination h3
        · have : C 0 1 * e = 0 := by rw [h1, hb]; ring
          have := (mul_eq_zero.1 this).resolve_right he
          rw [hb]; simp [this]
        · field_simp
    · refine ⟨C 0 1 / b, ?_, ?_, ?_⟩
      · field_simp
        linear_combination h2'
      · field_simp
      · field_simp
        linear_combination -h1
  obtain ⟨d, hd1, hd2, hd3⟩ := key
  refine ⟨(C 0 0 + C 1 1) / 2, d, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · field_simp; linear_combination hd1
  · exact hd2
  · exact hd3
  · field_simp; linear_combination -hd1

theorem decomp {q : ℕ} (hq : q % 4 = 1) (h2 : (2 : K) ≠ 0) (B C : Matrix (Fin 2) (Fin 2) K) (l : K)
    (hB : B * B = -1) (hBU : (B.map (· ^ q))ᵀ * B = 1) (hC : C * C = l • (1 : Matrix (Fin 2) (Fin 2) K))
    (hCB : C * B = B * C) :
    ∃ t d : K, C = t • (1 : Matrix (Fin 2) (Fin 2) K) + d • B ∧ t * d = 0 ∧ t * t - d * d = l := by
  have htr := tr_zero hq h2 B hB hBU
  have hBe : B = !![B 0 0, B 0 1; B 1 0, -B 0 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [htr]
  have hab : B 0 0 * B 0 0 + B 0 1 * B 1 0 = -1 := by
    have := congrFun (congrFun hB 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hCB' := hCB
  rw [hBe] at hCB'
  obtain ⟨t, d, hCd⟩ := commutant_two h2 (B 0 0) (B 0 1) (B 1 0) hab C hCB'
  rw [← hBe] at hCd
  have c00 : C 0 0 = t + d * B 0 0 := by simpa using congrFun (congrFun hCd 0) 0
  have c01 : C 0 1 = d * B 0 1 := by simpa using congrFun (congrFun hCd 0) 1
  have c10 : C 1 0 = d * B 1 0 := by simpa using congrFun (congrFun hCd 1) 0
  have c11 : C 1 1 = t - d * B 0 0 := by
    have := congrFun (congrFun hCd 1) 1
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, htr] at this
    linear_combination this
  have s00 := congrFun (congrFun hC 0) 0
  have s01 := congrFun (congrFun hC 0) 1
  have s10 := congrFun (congrFun hC 1) 0
  have s11 := congrFun (congrFun hC 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at s00 s01 s10 s11
  simp only [c00, c01, c10, c11] at s00 s01 s10 s11
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have e1 : t * d * B 0 0 = 0 := by
    have : (4 : K) * (t * d * B 0 0) = 0 := by linear_combination s00 - s11
    exact (mul_eq_zero.1 this).resolve_left h4
  have e2 : t * d * B 0 1 = 0 := by
    have : (2 : K) * (t * d * B 0 1) = 0 := by linear_combination s01
    exact (mul_eq_zero.1 this).resolve_left h2
  have e3 : t * d * B 1 0 = 0 := by
    have : (2 : K) * (t * d * B 1 0) = 0 := by linear_combination s10
    exact (mul_eq_zero.1 this).resolve_left h2
  have htd : t * d = 0 := by
    by_contra htd
    have a0 : B 0 0 = 0 := (mul_eq_zero.1 e1).resolve_left htd
    have b0 : B 0 1 = 0 := (mul_eq_zero.1 e2).resolve_left htd
    have e0 : B 1 0 = 0 := (mul_eq_zero.1 e3).resolve_left htd
    rw [a0, b0, e0] at hab
    exact one_ne_zero (by linear_combination hab)
  refine ⟨t, d, hCd, htd, ?_⟩
  rw [mul_eq_zero] at htd
  rcases htd with h0 | h0
  · rw [h0] at s00
    linear_combination s00 - d * d * hab + t * h0
  · rw [h0] at s00
    linear_combination s00 - d * h0

theorem norm_of_smul_one {q : ℕ} (t : K) (hU : (((t • (1 : Matrix (Fin 2) (Fin 2) K)).map (· ^ q))ᵀ *
    (t • (1 : Matrix (Fin 2) (Fin 2) K))) = 1) : t ^ q * t = 1 := by
  have := congrFun (congrFun hU 0) 0
  simpa [Matrix.mul_apply, Fin.sum_univ_two] using this

theorem norm_of_smul {q : ℕ} (B : Matrix (Fin 2) (Fin 2) K) (d : K)
    (hBU : (B.map (· ^ q))ᵀ * B = 1) (hU : ((d • B).map (· ^ q))ᵀ * (d • B) = 1) : d ^ q * d = 1 := by
  have e : ((d • B).map (· ^ q))ᵀ * (d • B) = (d ^ q * d) • ((B.map (· ^ q))ᵀ * B) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      mul_pow, Fin.sum_univ_two]
    ring
  rw [e, hBU] at hU
  have := congrFun (congrFun hU 0) 0
  simpa using this

theorem mixed_false {q : ℕ} (hq : q % 4 = 1) (h2 : (2 : K) ≠ 0) (t d : K) (htt : t * t = -(d * d))
    (ht : t ^ q * t = 1) (hd : d ^ q * d = 1) : False := by
  have hd0 : d ≠ 0 := fun h => by rw [h] at hd; simp at hd
  have hu : (t / d) * (t / d) = -1 := by
    field_simp
    linear_combination htt
  have hq1 := pow_eq_self_of_sq_neg_one hq hu
  have h1 : (t / d) ^ q * (t / d) = 1 := by
    rw [div_pow, div_mul_div_comm, ht, hd, div_one]
  rw [hq1, hu] at h1
  apply h2
  linear_combination -h1

theorem block_class {q : ℕ} (hq : q % 4 = 1) (h2 : (2 : K) ≠ 0) (B B' C C' : Matrix (Fin 2) (Fin 2) K) (l : K)
    (hB : B * B = -1) (hBU : (B.map (· ^ q))ᵀ * B = 1) (hB' : B' * B' = -1)
    (hB'U : (B'.map (· ^ q))ᵀ * B' = 1)
    (hC : C * C = l • (1 : Matrix (Fin 2) (Fin 2) K)) (hCU : (C.map (· ^ q))ᵀ * C = 1)
    (hC' : C' * C' = l • (1 : Matrix (Fin 2) (Fin 2) K)) (hC'U : (C'.map (· ^ q))ᵀ * C' = 1)
    (hCB : C * B = B * C) (hC'B' : C' * B' = B' * C') :
    ∃ μ : K, μ ≠ 0 ∧ ((C = μ • (1 : Matrix (Fin 2) (Fin 2) K) ∧ C' = μ • (1 : Matrix (Fin 2) (Fin 2) K)) ∨
      (C = μ • (1 : Matrix (Fin 2) (Fin 2) K) ∧ C' = -(μ • (1 : Matrix (Fin 2) (Fin 2) K))) ∨
      (C = μ • B ∧ C' = μ • B') ∨ (C = μ • B ∧ C' = -(μ • B'))) := by
  obtain ⟨t, d, hCd, htd, hl⟩ := decomp hq h2 B C l hB hBU hC hCB
  obtain ⟨t', d', hCd', htd', hl'⟩ := decomp hq h2 B' C' l hB' hB'U hC' hC'B'
  have hne : ∀ x : K, x ^ q * x = 1 → x ≠ 0 := fun x hx h => by rw [h] at hx; simp at hx
  rcases mul_eq_zero.1 htd with h0 | h0 <;> rcases mul_eq_zero.1 htd' with h0' | h0'
  ·
    rw [h0, zero_smul, zero_add] at hCd
    rw [h0', zero_smul, zero_add] at hCd'
    subst hCd hCd'
    have hd := norm_of_smul B d hBU hCU
    have hd' := norm_of_smul B' d' hB'U hC'U
    have hsq : d * d = d' * d' := by rw [h0] at hl; rw [h0'] at hl'; linear_combination -hl + hl'
    refine ⟨d, hne d hd, ?_⟩
    rcases mul_self_eq_mul_self_iff.1 hsq.symm with h | h
    · right; right; left; rw [h]; exact ⟨rfl, rfl⟩
    · right; right; right; rw [h, neg_smul]; exact ⟨rfl, rfl⟩
  ·
    exfalso
    rw [h0, zero_smul, zero_add] at hCd
    rw [h0', zero_smul, add_zero] at hCd'
    subst hCd hCd'
    have hd := norm_of_smul B d hBU hCU
    have ht' := norm_of_smul_one t' hC'U
    rw [h0] at hl; rw [h0'] at hl'
    exact mixed_false hq h2 t' d (by linear_combination hl' - hl) ht' hd
  ·
    exfalso
    rw [h0, zero_smul, add_zero] at hCd
    rw [h0', zero_smul, zero_add] at hCd'
    subst hCd hCd'
    have ht := norm_of_smul_one t hCU
    have hd' := norm_of_smul B' d' hB'U hC'U
    rw [h0] at hl; rw [h0'] at hl'
    exact mixed_false hq h2 t d' (by linear_combination hl - hl') ht hd'
  ·
    rw [h0, zero_smul, add_zero] at hCd
    rw [h0', zero_smul, add_zero] at hCd'
    subst hCd hCd'
    have ht := norm_of_smul_one t hCU
    have ht' := norm_of_smul_one t' hC'U
    have hsq : t * t = t' * t' := by rw [h0] at hl; rw [h0'] at hl'; linear_combination hl - hl'
    refine ⟨t, hne t ht, ?_⟩
    rcases mul_self_eq_mul_self_iff.1 hsq.symm with h | h
    · left; rw [h]; exact ⟨rfl, rfl⟩
    · right; left; rw [h, neg_smul]; exact ⟨rfl, rfl⟩


end GenLocU4ExtBd

end CFSG.GH74.Generic.BProg.B2
