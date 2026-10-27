module

public import CFSG.CGT.Stroth77.Types21x
public import CFSG.CGT.Stroth77.Types321
public import CFSG.CGT.Stroth77.Types32x
public import CFSG.CGT.Stroth77.TypesMore

public section

namespace CFSG.CGT.Stroth77

open Matrix

variable {k : Fin 3 → ℕ}

@[expose] def vecZ (k : Fin 3 → ℕ) (v : Fin 3 → ℤ) : Torus k := fun i => (v i : ZMod (2 ^ k i))

theorem matAct_vecZ (M : IntMat) (hM : Compat k M) (v : Fin 3 → ℤ) :
    matAct k M hM (vecZ k v) = vecZ k (M *ᵥ v) := by
  funext i
  rw [matAct_apply]
  simp only [vecZ, entryHom_intCast, Fin.sum_univ_three, Matrix.mulVec, dotProduct]
  push_cast
  ring

theorem vecZ_surjective (x : Torus k) : ∃ v, vecZ k v = x := by
  choose v hv using fun i => ZMod.intCast_surjective (x i)
  exact ⟨v, funext hv⟩

theorem vecZ_add (v w : Fin 3 → ℤ) : vecZ k (v + w) = vecZ k v + vecZ k w := by
  funext i
  simp [vecZ]

theorem neg_vecZ (v : Fin 3 → ℤ) : -vecZ k v = vecZ k (-v) := by
  funext i
  simp [vecZ]

theorem vecZ_eq_iff {v w : Fin 3 → ℤ} :
    vecZ k v = vecZ k w ↔ ∀ i, (2 : ℤ) ^ k i ∣ w i - v i := by
  simp only [vecZ, funext_iff, ZMod.intCast_eq_intCast_iff_dvd_sub]
  push_cast
  rfl

theorem exists_vecZ_eq_two_nsmul {v : Fin 3 → ℤ} (h : ∀ i, 2 ∣ v i) :
    ∃ w : Torus k, vecZ k v = 2 • w := by
  choose q hq using h
  refine ⟨vecZ k q, funext fun i => ?_⟩
  simp only [vecZ, Pi.smul_apply, nsmul_eq_mul, hq i]
  push_cast
  ring

theorem vecZ_ne_two_nsmul {j : Fin 3} (hj : 1 ≤ k j) {v : Fin 3 → ℤ} (hv : ¬ 2 ∣ v j)
    (w : Torus k) : vecZ k v ≠ 2 • w := by
  intro h
  have h1 := congrArg (ZMod.castHom (dvd_pow_self 2 (by omega : k j ≠ 0)) (ZMod 2))
    (congrFun h j)
  have h2 : ∀ z : ZMod 2, 2 • z = 0 := by decide
  simp only [vecZ, Pi.smul_apply, map_intCast, map_nsmul, h2] at h1
  exact hv ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h1)

theorem not_intertwine_of_inv {φ ψ : Torus k →+ Torus k} {x y w₀ : Torus k}
    (hx : φ x = -x) (hy : φ y = -y) (hx2 : ∀ z, x ≠ 2 • z) (hy2 : ∀ z, y ≠ 2 • z)
    (hxy2 : ∀ z, x + y ≠ 2 • z)
    (hψ : ∀ z, ψ z = -z → (∃ v, z = 2 • v) ∨ ∃ v, z = w₀ + 2 • v)
    (g : Torus k ≃+ Torus k) : ¬ ∀ z, g (φ z) = ψ (g z) := by
  intro hg
  have hinv : ∀ z, φ z = -z → ψ (g z) = -g z := fun z hz => by rw [← hg, hz, map_neg]
  have h2 : ∀ z v, g z = 2 • v → z = 2 • g.symm v := fun z v h => by
    rw [← map_nsmul, ← h, AddEquiv.symm_apply_apply]
  rcases hψ _ (hinv x hx) with ⟨v, hv⟩ | ⟨v, hv⟩
  · exact hx2 _ (h2 _ _ hv)
  rcases hψ _ (hinv y hy) with ⟨v', hv'⟩ | ⟨v', hv'⟩
  · exact hy2 _ (h2 _ _ hv')
  refine hxy2 _ (h2 _ (w₀ + v + v') ?_)
  rw [map_add, hv, hv']
  module

theorem inv_cases_of_even {v : Fin 3 → ℤ} (h0 : 2 ∣ v 0) (h12 : 2 ∣ v 1 + v 2) :
    (∃ w : Torus k, vecZ k v = 2 • w) ∨ ∃ w : Torus k, vecZ k v = vecZ k ![0, 1, 1] + 2 • w := by
  rcases Int.emod_two_eq_zero_or_one (v 1) with h | h
  · left
    refine exists_vecZ_eq_two_nsmul fun i => ?_
    fin_cases i
    · exact h0
    · exact Int.dvd_of_emod_eq_zero h
    · change 2 ∣ v 2
      omega
  · right
    obtain ⟨w, hw⟩ := exists_vecZ_eq_two_nsmul (k := k) (v := v - ![0, 1, 1]) fun i => by
      fin_cases i
      · simpa using h0
      · change 2 ∣ v 1 - 1
        omega
      · change 2 ∣ v 2 - 1
        omega
    refine ⟨w, ?_⟩
    rw [← hw, ← vecZ_add, add_sub_cancel]

theorem not_intertwine_uv_u_type300 {n : ℕ} (hn : 2 ≤ n)
    (g : Torus (Type300.k n) ≃+ Torus (Type300.k n)) :
    ¬ ∀ x, g ((Type300.action n).φuv x) = (Type300.action n).φu (g x) := by
  have hk : ∀ i, Type300.k n i = n := fun i => by fin_cases i <;> rfl
  have h1 : ∀ i, 1 ≤ Type300.k n i := fun i => by rw [hk]; omega
  refine not_intertwine_of_inv (x := vecZ _ ![2, 1, 0]) (y := vecZ _ ![2, 0, 1])
    (w₀ := vecZ _ ![0, 1, 1]) ?_ ?_ (vecZ_ne_two_nsmul (j := 1) (h1 1) (by decide))
    (vecZ_ne_two_nsmul (j := 2) (h1 2) (by decide)) ?_ ?_ g
  · rw [SigmaFourAction.φuv, matAct_vecZ, neg_vecZ, vecZ_eq_iff]
    intro i
    fin_cases i <;> simp [Type300.action, SigmaFourAction.ofMatEq, Type300.uvM, Type300.uvA,
      Type300.tM, Type300.ρM, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      -Matrix.mulVec_mulVec]
  · rw [SigmaFourAction.φuv, matAct_vecZ, neg_vecZ, vecZ_eq_iff]
    intro i
    fin_cases i <;> simp [Type300.action, SigmaFourAction.ofMatEq, Type300.uvM, Type300.uvA,
      Type300.tM, Type300.ρM, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      -Matrix.mulVec_mulVec]
  · intro z
    rw [← vecZ_add]
    exact vecZ_ne_two_nsmul (j := 1) (h1 1) (by decide) z
  · intro z hz
    obtain ⟨v, rfl⟩ := vecZ_surjective z
    rw [SigmaFourAction.φu, matAct_vecZ, neg_vecZ, vecZ_eq_iff] at hz
    have h0 := hz 0
    have h12 := hz 1
    simp only [hk, Type300.action, SigmaFourAction.ofMatEq, Type300.uM, uMat, ofCols_apply,
      Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Pi.neg_apply] at h0 h12
    simp at h0 h12
    have h4 : (4 : ℤ) ∣ 2 ^ n := by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num]
      exact pow_dvd_pow 2 hn
    have h2 : (2 : ℤ) ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    apply inv_cases_of_even
    · have := h4.trans h0
      omega
    · have := h2.trans h12
      omega

theorem not_intertwine_uv_u_type310 {m : ℕ} (hm : 3 ≤ m)
    (g : Torus (Type310.k m) ≃+ Torus (Type310.k m)) :
    ¬ ∀ x, g ((Type310.action m (by omega)).φuv x) = (Type310.action m (by omega)).φu (g x) := by
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 3 := ⟨m - 3, by omega⟩
  have hk : ∀ i, Type310.k (s + 3) i = s + 3 := fun i => by fin_cases i <;> rfl
  have h1 : ∀ i, 1 ≤ Type310.k (s + 3) i := fun i => by rw [hk]; omega
  have hsub : s + 3 - 2 = s + 1 := by omega
  refine not_intertwine_of_inv (x := vecZ _ ![2, 1, 0]) (y := vecZ _ ![2, 0, 1])
    (w₀ := vecZ _ ![0, 1, 1]) ?_ ?_ (vecZ_ne_two_nsmul (j := 1) (h1 1) (by decide))
    (vecZ_ne_two_nsmul (j := 2) (h1 2) (by decide)) ?_ ?_ g
  · rw [SigmaFourAction.φuv, matAct_vecZ, neg_vecZ, vecZ_eq_iff]
    intro i
    fin_cases i <;> simp [hk, hsub, Type310.action, SigmaFourAction.ofMatEq, Type310.uvM,
      Type310.uvA, Type310.tM, Type310.ρM, ofCols_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, -Matrix.mulVec_mulVec]
    · exact ⟨-1, by ring⟩
  · rw [SigmaFourAction.φuv, matAct_vecZ, neg_vecZ, vecZ_eq_iff]
    intro i
    fin_cases i <;> simp [hk, hsub, Type310.action, SigmaFourAction.ofMatEq, Type310.uvM,
      Type310.uvA, Type310.tM, Type310.ρM, ofCols_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, -Matrix.mulVec_mulVec]
    · exact ⟨8, by ring⟩
    · exact ⟨1, by ring⟩
    · exact ⟨2, by ring⟩
  · intro z
    rw [← vecZ_add]
    exact vecZ_ne_two_nsmul (j := 1) (h1 1) (by decide) z
  · intro z hz
    obtain ⟨v, rfl⟩ := vecZ_surjective z
    rw [SigmaFourAction.φu, matAct_vecZ, neg_vecZ, vecZ_eq_iff] at hz
    have h0 := hz 0
    have h12 := hz 1
    simp only [hk, hsub, Type310.action, SigmaFourAction.ofMatEq, Type310.uM, uMat, ofCols_apply,
      Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Pi.neg_apply] at h0 h12
    simp at h0 h12
    have h4 : (4 : ℤ) ∣ 2 ^ (s + 3) := ⟨2 ^ (s + 1), by ring⟩
    have h2 : (2 : ℤ) ∣ 2 ^ (s + 3) := ⟨2 ^ (s + 2), by ring⟩
    apply inv_cases_of_even
    · have h := h4.trans h0
      have e : -v 0 - (2 * 2 ^ (s + 1) + 1) * v 0 = -2 * v 0 - 4 * (2 ^ s * v 0) := by ring
      rw [e] at h
      generalize 2 ^ s * v 0 = X at h
      omega
    · have := h2.trans h12
      omega

theorem not_intertwine_uv_u_type331 (g : Torus Type331.k ≃+ Torus Type331.k) :
    ¬ ∀ x, g (Type331.action.φuv x) = Type331.action.φu (g x) := by
  have h1 : ∀ i, 1 ≤ Type331.k i := fun i => by fin_cases i <;> decide
  refine not_intertwine_of_inv (x := vecZ _ ![2, 0, 1]) (y := vecZ _ ![0, 1, 1])
    (w₀ := vecZ _ ![0, 1, 1]) ?_ ?_ (vecZ_ne_two_nsmul (j := 2) (h1 2) (by decide))
    (vecZ_ne_two_nsmul (j := 1) (h1 1) (by decide)) ?_ ?_ g
  · rw [SigmaFourAction.φuv, matAct_vecZ, neg_vecZ, vecZ_eq_iff]
    intro i
    fin_cases i <;> simp [Type331.action, SigmaFourAction.ofMatEq, Type331.uvM, Type331.uvA,
      Type331.tM, Type331.ρM, Type331.k, ofCols_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, -Matrix.mulVec_mulVec] <;> decide
  · rw [SigmaFourAction.φuv, matAct_vecZ, neg_vecZ, vecZ_eq_iff]
    intro i
    fin_cases i <;> simp [Type331.action, SigmaFourAction.ofMatEq, Type331.uvM, Type331.uvA,
      Type331.tM, Type331.ρM, Type331.k, ofCols_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, -Matrix.mulVec_mulVec] <;> decide
  · intro z
    rw [← vecZ_add]
    exact vecZ_ne_two_nsmul (j := 1) (h1 1) (by decide) z
  · intro z hz
    obtain ⟨v, rfl⟩ := vecZ_surjective z
    rw [SigmaFourAction.φu, matAct_vecZ, neg_vecZ, vecZ_eq_iff] at hz
    have h0 := hz 0
    have h12 := hz 1
    simp [Type331.action, SigmaFourAction.ofMatEq, Type331.uM, Type331.k, uMat, ofCols_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h12
    apply inv_cases_of_even
    · omega
    · omega

theorem type330_uv_inv {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) :
    (∀ r, (2 : ℤ) ^ Type330.k m r ∣
      (-![2, 0, 1] : Fin 3 → ℤ) r - (Type330.uvM i F G N *ᵥ ![2, 0, 1]) r) ∧
    (∀ r, (2 : ℤ) ^ Type330.k m r ∣
      (-![0, 1, G + 2] : Fin 3 → ℤ) r - (Type330.uvM i F G N *ᵥ ![0, 1, G + 2]) r) := by
  obtain ⟨hm, hi, hF, hG, hN⟩ := h
  subst hi hF hN
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, by omega⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = 2 ^ s := ⟨2 ^ s, rfl⟩
  have hsub : s + 2 - 1 = s + 1 := rfl
  have hNn : (2 : ℤ) ^ (s + 1) = 2 * n := by rw [hn, pow_succ]; ring
  have hG' : 3 * G + 7 = 4 * n * n := by
    rw [hG, hsub, hNn]
    ring
  have h2m : ∀ r : Fin 3, (2 : ℤ) ^ Type330.k (s + 2) r = 4 * n := by
    intro r
    have : Type330.k (s + 2) r = s + 2 := by fin_cases r <;> rfl
    rw [this, hn, pow_add]
    norm_num
    ring
  have key : ∀ (E : ℕ) (d W : ℤ), 3 ^ E * d = 4 * n * W → 4 * n ∣ d := by
    intro E d W hd
    have h4 : 4 * n = 2 ^ (s + 2) := by rw [hn, pow_add]; ring
    rw [h4] at hd ⊢
    have h3 : IsCoprime ((2 : ℤ) ^ (s + 2)) ((3 : ℤ) ^ E) := by
      have hodd : Odd ((3 : ℤ) ^ E) := (show Odd (3 : ℤ) by exact ⟨1, by norm_num⟩).pow
      exact hodd.isCoprime_two.symm.pow_left
    exact Int.dvd_of_dvd_mul_right_of_gcd_one ⟨W, hd⟩ (Int.isCoprime_iff_gcd_eq_one.mp h3)
  refine ⟨fun r => ?_, fun r => ?_⟩ <;> rw [h2m r] <;> fin_cases r
  · refine key 2 _ (8192 * n ^ 5 + 4096 * n ^ 4 + 9728 * n ^ 3 - 128 * n ^ 2 + 440 * n - 8) ?_
    simp [hsub, hNn, Type330.uvM, Type330.uvA, Type330.tM, Type330.ρM, ofCols_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, -Matrix.mulVec_mulVec]
    linear_combination (4608 * G ^ 2 + (6144 * n ^ 2 + 3072 * n + 28800) * G + 8192 * n ^ 4 +
      4096 * n ^ 3 +
      24064 * n ^ 2 + 7040 * n + 42552) * hG'
  · refine key 2 _ (1024 * n ^ 4 + 7680 * n ^ 3 - 32 * n ^ 2 + 384 * n - 11) ?_
    simp [hsub, hNn, Type330.uvM, Type330.uvA, Type330.tM, Type330.ρM, ofCols_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, -Matrix.mulVec_mulVec]
    linear_combination ((768 * n + 5760) * G + 1024 * n ^ 3 + 7680 * n ^ 2 + 1760 * n + 13824) * hG'
  · refine key 2 _ (1024 * n ^ 4 - 768 * n ^ 3 - 32 * n ^ 2 - 96 * n - 2) ?_
    simp [hsub, hNn, Type330.uvM, Type330.uvA, Type330.tM, Type330.ρM, ofCols_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, -Matrix.mulVec_mulVec]
    linear_combination ((768 * n - 576) * G + 1024 * n ^ 3 - 768 * n ^ 2 + 1760 * n - 1440) * hG'
  · refine key 3 _ (32768 * n ^ 7 + 16384 * n ^ 6 + 30720 * n ^ 5 - 4608 * n ^ 4 - 9696 * n ^ 3 +
      96 * n ^ 2 - 332 * n + 8) ?_
    simp [hsub, hNn, Type330.uvM, Type330.uvA, Type330.tM, Type330.ρM, ofCols_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, -Matrix.mulVec_mulVec]
    linear_combination (13824 * G ^ 3 + (18432 * n ^ 2 + 9216 * n + 114048) * G ^ 2 +
      (24576 * n ^ 4 + 12288 * n ^ 3 + 109056 * n ^ 2 + 39552 * n + 299160) * G +
      32768 * n ^ 6 + 16384 * n ^ 5 + 88064 * n ^ 4 + 24064 * n ^ 3 + 144416 * n ^ 2 +
      42208 * n + 252396) * hG'
  · refine key 3 _ (4096 * n ^ 6 + 30720 * n ^ 5 - 1152 * n ^ 4 - 6144 * n ^ 3 + 24 * n ^ 2 -
      6 * n + 2) ?_
    simp [hsub, hNn, Type330.uvM, Type330.uvA, Type330.tM, Type330.ρM, ofCols_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, -Matrix.mulVec_mulVec]
    linear_combination ((2304 * n + 17280) * G ^ 2 +
      (3072 * n ^ 3 + 23040 * n ^ 2 + 9888 * n + 76032) * G +
      4096 * n ^ 5 + 30720 * n ^ 4 + 6016 * n ^ 3 + 47616 * n ^ 2 + 10552 * n + 83322) * hG'
  · refine key 3 _ (4096 * n ^ 6 - 3072 * n ^ 5 - 1152 * n ^ 4 + 384 * n ^ 3 + 24 * n ^ 2 -
      66 * n + 2) ?_
    simp [hsub, hNn, Type330.uvM, Type330.uvA, Type330.tM, Type330.ρM, ofCols_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, -Matrix.mulVec_mulVec]
    linear_combination ((2304 * n - 1728) * G ^ 2 +
      (3072 * n ^ 3 - 2304 * n ^ 2 + 9888 * n - 7776) * G +
      4096 * n ^ 5 - 3072 * n ^ 4 + 6016 * n ^ 3 - 4992 * n ^ 2 + 10552 * n - 8802) * hG'

theorem type330_u_inv {m : ℕ} {i F G N : ℤ} (h : Type32x.Data m i F G N) (v : Fin 3 → ℤ)
    (hz : ∀ r, (2 : ℤ) ^ Type330.k m r ∣ (-v) r - (Type330.uM F N *ᵥ v) r) :
    (∃ w : Torus (Type330.k m), vecZ _ v = 2 • w) ∨
      ∃ w : Torus (Type330.k m), vecZ _ v = vecZ _ ![0, 1, 1] + 2 • w := by
  obtain ⟨hm, -, -, -, hN⟩ := h
  have hk : ∀ r, Type330.k m r = m := fun r => by fin_cases r <;> rfl
  have e0 : (Type330.uM F N *ᵥ v) 0 = (N - 1) * v 0 - 8 * F * v 1 + 8 * F * (N - 1) * v 2 := by
    simp [Type330.uM, uMat, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  have e1 : (Type330.uM F N *ᵥ v) 1 = v 2 := by
    simp [Type330.uM, uMat, ofCols_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have h0 := hz 0
  have h1 := hz 1
  rw [e0, Pi.neg_apply, hk] at h0
  rw [e1, Pi.neg_apply, hk] at h1
  have h2N : (2 : ℤ) ^ m = N * 2 := by
    rw [hN, ← pow_succ]
    congr 1
    omega
  obtain ⟨q, hq⟩ := h1
  have hv2 : v 2 = -v 1 - N * 2 * q := by rw [← h2N]; linarith
  have hE : -v 0 - ((N - 1) * v 0 - 8 * F * v 1 + 8 * F * (N - 1) * v 2) =
      N * (-v 0 + 8 * (F * v 1) + 16 * (F * (N - 1) * q)) := by
    rw [hv2]
    ring
  rw [hE, h2N] at h0
  have hNne : N ≠ 0 := by
    rw [hN]
    positivity
  have h0' := (mul_dvd_mul_iff_left hNne).mp h0
  have h12 : (2 : ℤ) ∣ -v 1 - v 2 := ⟨N * q, by rw [hq, h2N]; ring⟩
  apply inv_cases_of_even
  · generalize F * v 1 = A at h0'
    generalize F * (N - 1) * q = B at h0'
    omega
  · omega

theorem not_intertwine_uv_u_type330 {m : ℕ} (hm : 3 ≤ m)
    (g : Torus (Type330.k m) ≃+ Torus (Type330.k m)) :
    ¬ ∀ x, g ((Type330.actionPaper m hm).φuv x) = (Type330.actionPaper m hm).φu (g x) := by
  have hdata := Type32x.data m (Nat.le_trans (by norm_num) hm)
  obtain ⟨hx, hy⟩ := type330_uv_inv hdata
  have hk : ∀ i, Type330.k m i = m := fun i => by fin_cases i <;> rfl
  have h1 : ∀ i, 1 ≤ Type330.k m i := fun i => by rw [hk]; omega
  refine not_intertwine_of_inv (x := vecZ _ ![2, 0, 1]) (y := vecZ _ ![0, 1, Type120.GV m + 2])
    (w₀ := vecZ _ ![0, 1, 1]) ?_ ?_ (vecZ_ne_two_nsmul (j := 2) (h1 2) (by decide))
    (vecZ_ne_two_nsmul (j := 1) (h1 1) (by simp)) ?_ ?_ g
  · rw [SigmaFourAction.φuv, matAct_vecZ, neg_vecZ, vecZ_eq_iff]
    exact hx
  · rw [SigmaFourAction.φuv, matAct_vecZ, neg_vecZ, vecZ_eq_iff]
    exact hy
  · intro z
    rw [← vecZ_add]
    exact vecZ_ne_two_nsmul (j := 1) (h1 1) (by simp) z
  · intro z hz
    obtain ⟨v, rfl⟩ := vecZ_surjective z
    rw [SigmaFourAction.φu, matAct_vecZ, neg_vecZ, vecZ_eq_iff] at hz
    exact type330_u_inv hdata v hz

end CFSG.CGT.Stroth77
