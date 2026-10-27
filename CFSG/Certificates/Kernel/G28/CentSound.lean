module

public import Certificates.Data.Kernel.G28.Cent
public import CFSG.Certificates.Kernel.G28.Sound
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G28CentCheck

public section

namespace CFSG.KC.G28

open CFSG.Quasithin CFSG.RankThree.PartTwo.Sec4.Item434G28
open scoped Matrix

theorem ent_codeP {A : Array ℕ} (hA : Valid A) {t : ℕ} (ht : t < 36) :
    ent (codeP A) t = A[t]! := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [ent, fld_bit]
  by_cases hq : q < 3
  · rw [decide_eq_true hq, Bool.true_and]
    exact codeP_bit hA t q hq
  · rw [decide_eq_false hq, Bool.false_and]
    refine (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (hA.2 t ht) ?_)).symm
    calc 8 = 2 ^ 3 := rfl
      _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem codeP_eq_of_ent {X : Array ℕ} (hX : Valid X) {N : ℕ} (hN : N < 2 ^ 108)
    (h : ∀ t < 36, X[t]! = ent N t) : codeP X = N := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 108
  · obtain ⟨t, s, ht, hs, rfl⟩ : ∃ t s, t < 36 ∧ s < 3 ∧ p = 3 * t + s :=
      ⟨p / 3, p % 3, by omega, by omega, by omega⟩
    rw [codeP_bit hX t s hs, h t ht, ent, fld_bit, decide_eq_true hs, Bool.true_and]
    rfl
  · rw [testBit_of_lt (codeP_lt hX) (by omega), testBit_of_lt hN (by omega)]

theorem entsOK_spec {x : ℕ} {f : ℕ → ℕ} (h : entsOK x f = true) :
    x < 2 ^ 108 ∧ ∀ t < 36, ent x t = f t := by
  simp only [entsOK, Bool.and_eq_true, Nat.blt_eq, List.all_eq_true, List.mem_range,
    Nat.beq_eq] at h
  exact h

theorem cond_beq (a b x y : ℕ) : cond (Nat.beq a b) x y = if a = b then x else y := by
  cases hb : Nat.beq a b
  · rw [if_neg (Nat.ne_of_beq_eq_false hb)]
    rfl
  · rw [if_pos (Nat.eq_of_beq_eq_true hb)]
    rfl

theorem gf8_add_self : ∀ c : GF8, c + c = 0 := by decide

theorem gf8_pow_eight : ∀ c : GF8, c ^ 8 = c := by decide

theorem mat_add_self (A : Matrix (Fin 6) (Fin 6) GF8) : A + A = 0 := by
  ext i j
  rw [Matrix.add_apply, Matrix.zero_apply]
  exact gf8_add_self _

theorem sq_add_of_commute {x y : Matrix (Fin 6) (Fin 6) GF8} (h : Commute x y) :
    (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  have h2 : x * y + y * x = 0 := by
    rw [h.eq]
    exact mat_add_self _
  rw [sq, sq, sq, add_mul, mul_add, mul_add]
  calc x * x + x * y + (y * x + y * y) = x * x + y * y + (x * y + y * x) := by abel
    _ = x * x + y * y := by rw [h2, add_zero]

theorem pow_eight_add_of_commute {x y : Matrix (Fin 6) (Fin 6) GF8} (h : Commute x y) :
    (x + y) ^ 8 = x ^ 8 + y ^ 8 := by
  have e : ∀ a : Matrix (Fin 6) (Fin 6) GF8, a ^ 8 = ((a ^ 2) ^ 2) ^ 2 := fun a => by
    rw [← pow_mul, ← pow_mul]
  rw [e, e x, e y, sq_add_of_commute h, sq_add_of_commute (h.pow_pow 2 2),
    sq_add_of_commute ((h.pow_pow 2 2).pow_pow 2 2)]

theorem pow_eight_sum (s : Finset (Fin 6)) (f : Fin 6 → Matrix (Fin 6) (Fin 6) GF8)
    (hc : ∀ i j, Commute (f i) (f j)) : (∑ i ∈ s, f i) ^ 8 = ∑ i ∈ s, f i ^ 8 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      pow_eight_add_of_commute (Commute.sum_right _ _ _ fun j _ => hc a j), ih]

theorem pow_nine_of_frob {q : Fin 6 → Matrix (Fin 6) (Fin 6) GF8} {J : Matrix (Fin 6) (Fin 6) GF8}
    (hc : ∀ i j, q i * q j = q j * q i) (hJ : J * J = 1) (hf : ∀ i, J * (q i)ᵀ * J = q i ^ 8)
    (w : Fin 6 → GF8) (hs : (∑ i, w i • q i)ᵀ * J * (∑ i, w i • q i) = J) :
    (∑ i, w i • q i) ^ 9 = 1 := by
  set M := ∑ i, w i • q i with hM
  have h8 : M ^ 8 = J * Mᵀ * J := by
    rw [hM, pow_eight_sum _ _ fun i j =>
      (Commute.smul_left (hc i j) (w i)).smul_right (w j)]
    rw [Matrix.transpose_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_pow, gf8_pow_eight, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, hf]
  have e9 : M ^ 9 = M ^ 8 * M := pow_succ M 8
  rw [e9, h8, mul_assoc, mul_assoc, ← mul_assoc Mᵀ, hs, hJ]

theorem centAll_of {Q : Array (Array ℕ)} (hQ : ∀ i < 6, Valid Q[i]!)
    (hc : ∀ i < 6, ∀ k < 6, mulCode Q[i]! Q[k]! = mulCode Q[k]! Q[i]!)
    (hf : ∀ i < 6, mulCode (mulCode jCode (transCode Q[i]!)) jCode = powCode Q[i]! 8)
    (hJ : mulCode jCode jCode = idCode) : centAll Q = true := by
  simp only [centAll, List.all_eq_true, List.mem_range]
  intro a0 h0 a1 h1 a2 h2 a3 h3 a4 h4 a5 h5
  have hw : ∀ i < 6, (#[a0, a1, a2, a3, a4, a5] : Array ℕ)[i]! < 8 := by
    intro i hi
    interval_cases i <;> simp [h0, h1, h2, h3, h4, h5]
  have hMv : Valid (linCode #[a0, a1, a2, a3, a4, a5] Q) := valid_linCode hw hQ
  have hdec := decode_linCode hw hQ
  have hJv := valid_jCode
  simp only [centAt, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  by_cases hs : mulCode (mulCode (transCode (linCode #[a0, a1, a2, a3, a4, a5] Q)) jCode)
      (linCode #[a0, a1, a2, a3, a4, a5] Q) = jCode
  · right
    have hs' := congrArg decode hs
    rw [decode_mulCode (valid_mulCode (valid_transCode hMv) hJv) hMv,
      decode_mulCode (valid_transCode hMv) hJv, decode_transCode, hdec] at hs'
    have hdJ : decode jCode * decode jCode = 1 := by
      rw [← decode_mulCode hJv hJv, hJ, decode_idCode]
    apply eq_of_decode_eq (valid_powCode hMv 9) valid_idCode
    rw [decode_powCode hMv, decode_idCode, hdec]
    refine pow_nine_of_frob (q := fun i => decode Q[i.val]!) (J := decode jCode) ?_ hdJ ?_ _ hs'
    · intro i j
      rw [← decode_mulCode (hQ i i.2) (hQ j j.2), ← decode_mulCode (hQ j j.2) (hQ i i.2),
        hc i i.2 j j.2]
    · intro i
      have h := congrArg decode (hf i i.2)
      rw [decode_mulCode (valid_mulCode hJv (valid_transCode (hQ i i.2))) hJv,
        decode_mulCode hJv (valid_transCode (hQ i i.2)), decode_transCode,
        decode_powCode (hQ i i.2)] at h
      exact h
  · left
    exact hs

theorem centOK_of {u z : Array ℕ} (hu : Valid u) (hz : Valid z) {v0 b binv : Array ℕ}
    (hb : Valid b) (hbi : Valid binv) (hv0 : v0.size = 6 ∧ ∀ i < 6, v0[i]! < 8)
    {vP jP : ℕ} {gs cp q qt : List ℕ}
    (h : centP (codeP u) (codeP z) v0.toList vP jP (codeP b) (codeP binv) gs cp q qt = true) :
    centOK (e0List u z) v0 b binv = true := by
  simp only [centP, Bool.and_eq_true, List.all_eq_true, List.mem_range, Nat.beq_eq,
    letB_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, hj⟩, hg⟩, hcol⟩, hbb⟩, hcp⟩, hq⟩, hqt⟩, hcomm⟩, hfrob⟩, hjj⟩ := h
  have hgv : ∀ k < 6, Valid (e0List u z)[k]! := fun k hk => valid_e0List hu hz (by omega)
  have hgP : ∀ k < 6, codeP (e0List u z)[k]! = gs.getD k 0 := by
    intro k hk
    rw [getElem!_e0List u z (by omega), codeP_mulCode (valid_powCode hu _) (valid_powCode hz _),
      codeP_powCode hu, codeP_powCode hz]
    exact (hg k hk).symm
  have hVv : Valid (vecCode v0) := valid_vecCode hv0.2
  have hvP : codeP (vecCode v0) = vP := by
    refine codeP_eq_of_ent hVv (entsOK_spec hv).1 fun t ht => ?_
    rw [(entsOK_spec hv).2 t ht, vecCode, getElem!_ofFn_nat' _ ht, vecE, cond_beq]
    dsimp only
    simp only [getElem!_nat]
    rfl
  have hJv := valid_jCode
  have hjP : codeP jCode = jP := by
    refine codeP_eq_of_ent hJv (entsOK_spec hj).1 fun t ht => ?_
    rw [(entsOK_spec hj).2 t ht, jCode, getElem!_ofFn_nat' _ ht, jE, cond_beq]
    rfl
  have hcP : ∀ i < 6, codeP (cCode (e0List u z) i) = cp.getD i 0 := by
    intro i hi
    refine codeP_eq_of_ent (valid_cCode hgv hi) (entsOK_spec (hcp i hi)).1 fun t ht => ?_
    rw [(entsOK_spec (hcp i hi)).2 t ht, cCode, getElem!_ofFn_nat' _ ht]
    have e := ent_codeP (hgv (t % 6) (by omega)) (by omega : 6 * (t / 6) + i < 36)
    rw [hgP _ (by omega)] at e
    exact e.symm
  have hQv : ∀ i < 6, Valid (qCodes (e0List u z) binv)[i]! := by
    intro i hi
    rw [qCodes_get _ _ hi]
    exact valid_mulCode (valid_cCode hgv hi) hbi
  have hQP : ∀ i < 6, codeP (qCodes (e0List u z) binv)[i]! = q.getD i 0 := by
    intro i hi
    rw [qCodes_get _ _ hi, codeP_mulCode (valid_cCode hgv hi) hbi, hcP i hi]
    exact hq i hi
  have hQT : ∀ i < 6, codeP (transCode (qCodes (e0List u z) binv)[i]!) = qt.getD i 0 := by
    intro i hi
    refine codeP_eq_of_ent (valid_transCode (hQv i hi)) (entsOK_spec (hqt i hi)).1 fun t ht => ?_
    rw [(entsOK_spec (hqt i hi)).2 t ht, transCode, getElem!_ofFn_nat' _ ht]
    have e := ent_codeP (hQv i hi) (by omega : 6 * (t % 6) + t / 6 < 36)
    rw [hQP i hi] at e
    exact e.symm
  simp only [centOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq]
  refine ⟨⟨⟨⟨⟨hb, hbi⟩, hv0⟩, fun k hk => ⟨hgv k hk, fun r hr => ?_⟩⟩, ?_⟩, ?_⟩
  · rw [← ent_codeP hb (by omega : 6 * r + k < 36),
      ← ent_codeP (valid_mulCode (hgv k hk) hVv) (by omega : 6 * r < 36),
      codeP_mulCode (hgv k hk) hVv, hgP k hk, hvP]
    exact hcol k hk r hr
  · exact codeP_inj (valid_mulCode hb hbi) valid_idCode
      (by rw [codeP_mulCode hb hbi, codeP_idCode]; exact hbb)
  · refine centAll_of hQv (fun i hi k hk => codeP_comm (hQv i hi) (hQv k hk) ?_)
      (fun i hi => ?_) ?_
    · rw [hQP i hi, hQP k hk]
      exact hcomm i hi k hk
    · refine codeP_inj (valid_mulCode (valid_mulCode hJv (valid_transCode (hQv i hi))) hJv)
        (valid_powCode (hQv i hi) 8) ?_
      rw [codeP_mulCode (valid_mulCode hJv (valid_transCode (hQv i hi))) hJv,
        codeP_mulCode hJv (valid_transCode (hQv i hi)), hjP, hQT i hi, codeP_powCode (hQv i hi),
        hQP i hi]
      exact hfrob i hi
    · refine codeP_inj (valid_mulCode hJv hJv) valid_idCode ?_
      rw [codeP_mulCode hJv hJv, hjP, codeP_idCode]
      exact hjj

end CFSG.KC.G28

end
