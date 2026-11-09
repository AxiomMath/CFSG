module

public import CFSG.Certificates.Kernel.O8PlusSound

public section

namespace CFSG.KC.O8

open CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] noncomputable def colMv (a r s : ℕ) : ℕ :=
  Nat.shiftLeft (Nat.land (Nat.shiftRight a r) low12) s

@[expose] noncomputable def rowMv (b r s : ℕ) : ℕ :=
  Nat.shiftLeft (Nat.land (Nat.shiftRight b (Nat.mul 12 s)) 4095) (Nat.mul 12 r)

@[expose] noncomputable def conPartE : List (ℕ × ℕ) → List (List ℕ) → ℕ → ℕ → ℕ
  | c :: cs, q :: qs, r, s => linComb q (colMv c.1 r s ^^^ rowMv c.2 r s) ^^^ conPartE cs qs r s
  | _, _, _, _ => 0

@[expose] noncomputable def linCheckE (cons : List (ℕ × ℕ)) (qc : List (List ℕ)) (qf fs : List ℕ) :
    Bool :=
  (List.range 144).all fun j =>
    (conPartE cons qc (j / 12) (j % 12) ^^^ linComb qf (freeBits fs (2 ^ j))) == 2 ^ j

theorem low12_testBit (q : ℕ) : low12.testBit q = decide (q < 144 ∧ q % 12 = 0) := by
  by_cases hq : q < 144
  · have h : ∀ q < 144, low12.testBit q = decide (q % 12 = 0) := by decide +kernel
    simp [h q hq, hq]
  · have h0 : low12 < 2 ^ 144 := by decide +kernel
    have h : low12 < 2 ^ q := lt_of_lt_of_le h0 (Nat.pow_le_pow_right (by norm_num) (by omega))
    simp [Nat.testBit_lt_two_pow h, hq]

theorem testBit_colMv (a r s p : ℕ) : (colMv a r s).testBit p =
    (decide (s ≤ p ∧ p - s < 144 ∧ (p - s) % 12 = 0) && a.testBit (p - s + r)) := by
  change (((a >>> r) &&& low12) <<< s).testBit p = _
  rw [Nat.testBit_shiftLeft, Nat.testBit_and, low12_testBit, Nat.testBit_shiftRight]
  by_cases h : s ≤ p <;> simp [h, Nat.add_comm r, Bool.and_comm]

theorem testBit_rowMv (b r s p : ℕ) : (rowMv b r s).testBit p =
    (decide (12 * r ≤ p ∧ p - 12 * r < 12) && b.testBit (12 * s + (p - 12 * r))) := by
  change (((b >>> (12 * s)) &&& 4095) <<< (12 * r)).testBit p = _
  rw [Nat.testBit_shiftLeft, Nat.testBit_and, show (4095 : ℕ) = 2 ^ 12 - 1 by norm_num,
    Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight]
  by_cases h : 12 * r ≤ p <;> simp [h, Bool.and_comm]

theorem testBit_unit (r s k j : ℕ) (hj : j < 12) (hs : s < 12) :
    (2 ^ (12 * r + s)).testBit (12 * k + j) = (decide (k = r) && decide (j = s)) := by
  rw [Nat.testBit_two_pow]
  by_cases hk : k = r <;> by_cases hjs : j = s <;> simp [hk, hjs] <;> omega

theorem testBit_mulK_lt (a b p : ℕ) (hp : 144 ≤ p) : (mulK a b).testBit p = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le (mulK_lt a b) (Nat.pow_le_pow_right (by norm_num) hp))

theorem testBit_mulK (a b : ℕ) {p : ℕ} (hp : p < 144) : bz ((mulK a b).testBit p) =
    ∑ k : Fin 12, bz (a.testBit (12 * (p / 12) + k)) * bz (b.testBit (12 * (k : ℕ) + p % 12)) := by
  have e := congrFun (congrFun (toMatK_mulK a b) ⟨p / 12, by omega⟩) ⟨p % 12, Nat.mod_lt _ (by norm_num)⟩
  simp only [toMatK, Matrix.of_apply, Matrix.mul_apply] at e
  rwa [Nat.div_add_mod] at e

theorem mulK_unit_right (a : ℕ) {r s : ℕ} (hr : r < 12) (hs : s < 12) :
    mulK a (2 ^ (12 * r + s)) = colMv a r s := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [testBit_colMv]
  by_cases hp : p < 144
  · have e := testBit_mulK a (2 ^ (12 * r + s)) hp
    rw [Finset.sum_eq_single ⟨r, hr⟩ (fun k _ hk => by
        rw [testBit_unit r s k _ (Nat.mod_lt _ (by norm_num)) hs]
        simp [Fin.ext_iff.not.mp hk]) (by simp),
      testBit_unit r s r _ (Nat.mod_lt _ (by norm_num)) hs, ← bz_and] at e
    rw [bz_injective e]
    by_cases hj : p % 12 = s
    · have h1 : s ≤ p ∧ p - s < 144 ∧ (p - s) % 12 = 0 := by omega
      have h2 : p - s + r = 12 * (p / 12) + r := by omega
      simp [hj, h1, h2]
    · have h1 : ¬ (s ≤ p ∧ p - s < 144 ∧ (p - s) % 12 = 0) := by omega
      simp [hj, h1]
  · have h1 : ¬ (s ≤ p ∧ p - s < 144 ∧ (p - s) % 12 = 0) := by omega
    simp [testBit_mulK_lt _ _ p (by omega), h1]

theorem mulK_unit_left (b : ℕ) {r s : ℕ} (hr : r < 12) (hs : s < 12) :
    mulK (2 ^ (12 * r + s)) b = rowMv b r s := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [testBit_rowMv]
  by_cases hp : p < 144
  · have e := testBit_mulK (2 ^ (12 * r + s)) b hp
    rw [Finset.sum_eq_single ⟨s, hs⟩ (fun k _ hk => by
        rw [testBit_unit r s (p / 12) k k.isLt hs]
        simp [Fin.ext_iff.not.mp hk]) (by simp),
      testBit_unit r s (p / 12) s hs hs, ← bz_and] at e
    rw [bz_injective e]
    by_cases hi : p / 12 = r
    · have h1 : 12 * r ≤ p ∧ p - 12 * r < 12 := by omega
      have h2 : 12 * s + (p - 12 * r) = 12 * s + p % 12 := by omega
      simp [hi, h1, h2]
    · have h1 : ¬ (12 * r ≤ p ∧ p - 12 * r < 12) := by omega
      simp [hi, h1]
  · have h1 : ¬ (12 * r ≤ p ∧ p - 12 * r < 12) := by omega
    simp [testBit_mulK_lt _ _ p (by omega), h1]

theorem conPartK_unit {r s : ℕ} (hr : r < 12) (hs : s < 12) :
    ∀ (cs : List (ℕ × ℕ)) (qs : List (List ℕ)),
      conPartK cs qs (2 ^ (12 * r + s)) = conPartE cs qs r s
  | c :: cs, q :: qs => by
    rw [conPartK, conPartE, ← mulK_eq, ← mulK_eq, mulK_unit_right _ hr hs, mulK_unit_left _ hr hs,
      conPartK_unit hr hs cs qs]
  | [], _ => by simp [conPartK, conPartE]
  | _ :: _, [] => by simp [conPartK, conPartE]

theorem linCheckWith_eq_E (cons : List (ℕ × ℕ)) (qc : List (List ℕ)) (qf fs : List ℕ) :
    linCheckWith cons qc qf fs = linCheckE cons qc qf fs := by
  rw [linCheckWith, linCheckE, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  refine forall_congr' fun j => imp_congr_right fun hj => ?_
  rw [List.mem_range] at hj
  have h : 2 ^ j = 2 ^ (12 * (j / 12) + j % 12) := by rw [Nat.div_add_mod]
  rw [linRec, conPart_eq, h, conPartK_unit (by omega) (Nat.mod_lt _ (by norm_num)), ← h]

@[expose] noncomputable def fget144 (P k : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight P (Nat.mul 144 k)) (2 ^ 144 - 1)

@[expose] noncomputable def packQ144 : List ℕ → ℕ
  | [] => 0
  | q :: qs => Nat.lor q (Nat.shiftLeft (packQ144 qs) 144)

@[expose] noncomputable def colUnit8 (a r s : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => cond (a.testBit (12 * k + r)) (2 ^ (12 * k + s)) 0 ^^^ colUnit8 a r s k

@[expose] noncomputable def rowUnit8 (b r s : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => cond (b.testBit (12 * s + k)) (2 ^ (12 * r + k)) 0 ^^^ rowUnit8 b r s k

@[expose] noncomputable def colPk8 (P a r s : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => cond (a.testBit (12 * k + r)) (fget144 P (12 * k + s)) 0 ^^^ colPk8 P a r s k

@[expose] noncomputable def rowPk8 (P b r s : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => cond (b.testBit (12 * s + k)) (fget144 P (12 * r + k)) 0 ^^^ rowPk8 P b r s k

@[expose] noncomputable def conPartP : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ
  | c :: cs, P :: Ps, r, s => colPk8 P c.1 r s 12 ^^^ rowPk8 P c.2 r s 12 ^^^ conPartP cs Ps r s
  | _, _, _, _ => 0

@[expose] noncomputable def linCheckP (cons : List (ℕ × ℕ)) (qc : List (List ℕ)) (qf fs : List ℕ) :
    Bool :=
  (qc.all fun q => q.all fun e => Nat.blt e (2 ^ 144)) &&
  (List.range 144).all fun j =>
    (conPartP cons (qc.map packQ144) (j / 12) (j % 12) ^^^ linComb qf (freeBits fs (2 ^ j))) == 2 ^ j

theorem fget144_eq (P k : ℕ) : fget144 P k = (P >>> (144 * k)) &&& (2 ^ 144 - 1) := rfl

theorem packQ144_cons (q : ℕ) (qs : List ℕ) : packQ144 (q :: qs) = q ||| packQ144 qs <<< 144 := rfl

theorem land_pack {q : ℕ} (X : ℕ) (hq : q < 2 ^ 144) : (q ||| X <<< 144) &&& (2 ^ 144 - 1) = q := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 144
  · have h : ¬ 144 ≤ i := by omega
    simp [hi, h]
  · have h : q < 2 ^ i := lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num) (by omega))
    simp [hi, Nat.testBit_lt_two_pow h]

theorem shiftRight_pack {q : ℕ} (X : ℕ) (hq : q < 2 ^ 144) : (q ||| X <<< 144) >>> 144 = X := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h : q < 2 ^ (144 + i) := lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_lt_two_pow h]
  simp

theorem linComb_two_pow : ∀ (q : List ℕ), (∀ e ∈ q, e < 2 ^ 144) → ∀ p : ℕ,
    linComb q (2 ^ p) = fget144 (packQ144 q) p
  | [], _, p => by simp [linComb, packQ144, fget144_eq]
  | q :: qs, h, p => by
    have hq := h q List.mem_cons_self
    rw [packQ144_cons, fget144_eq]
    cases p with
    | zero =>
      rw [Nat.mul_zero, Nat.shiftRight_zero, land_pack _ hq]
      simp [linComb, linComb_zero]
    | succ p =>
      have ih := linComb_two_pow qs (fun e he => h e (List.mem_cons_of_mem _ he)) p
      rw [fget144_eq] at ih
      have h2 : 2 ^ (p + 1) / 2 = 2 ^ p := by rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)]
      rw [linComb, Nat.testBit_two_pow, h2, ih, Nat.mul_succ, Nat.add_comm (144 * p) 144,
        Nat.shiftRight_add,
        shiftRight_pack _ hq]
      simp

theorem testBit_colUnit8 (a r s p : ℕ) : ∀ k : ℕ, (colUnit8 a r s k).testBit p =
    (decide (s ≤ p ∧ (p - s) % 12 = 0 ∧ (p - s) / 12 < k) && a.testBit (p - s + r))
  | 0 => by simp [colUnit8]
  | k + 1 => by
    rw [colUnit8, Nat.testBit_xor, testBit_colUnit8 a r s p k]
    by_cases hp : p = 12 * k + s
    · subst hp
      have h1 : 12 * k + s - s + r = 12 * k + r := by omega
      have h2 : ¬ (s ≤ 12 * k + s ∧ (12 * k + s - s) % 12 = 0 ∧ (12 * k + s - s) / 12 < k) := by
        omega
      have h3 : s ≤ 12 * k + s ∧ (12 * k + s - s) % 12 = 0 ∧ (12 * k + s - s) / 12 < k + 1 := by
        omega
      rw [h1, decide_eq_false h2, decide_eq_true h3]
      cases a.testBit (12 * k + r) <;> simp
    · have h2 : (s ≤ p ∧ (p - s) % 12 = 0 ∧ (p - s) / 12 < k + 1) ↔
          (s ≤ p ∧ (p - s) % 12 = 0 ∧ (p - s) / 12 < k) := by omega
      have h3 : (cond (a.testBit (12 * k + r)) (2 ^ (12 * k + s)) 0).testBit p = false := by
        cases a.testBit (12 * k + r) <;> simp [Ne.symm hp]
      rw [h3, Bool.false_xor]
      simp only [h2]

theorem testBit_rowUnit8 (b r s p : ℕ) : ∀ k : ℕ, (rowUnit8 b r s k).testBit p =
    (decide (12 * r ≤ p ∧ p - 12 * r < k) && b.testBit (12 * s + (p - 12 * r)))
  | 0 => by simp [rowUnit8]
  | k + 1 => by
    rw [rowUnit8, Nat.testBit_xor, testBit_rowUnit8 b r s p k]
    by_cases hp : p = 12 * r + k
    · subst hp
      have h1 : 12 * s + (12 * r + k - 12 * r) = 12 * s + k := by omega
      have h2 : ¬ (12 * r ≤ 12 * r + k ∧ 12 * r + k - 12 * r < k) := by omega
      have h3 : 12 * r ≤ 12 * r + k ∧ 12 * r + k - 12 * r < k + 1 := by omega
      rw [h1, decide_eq_false h2, decide_eq_true h3]
      cases b.testBit (12 * s + k) <;> simp
    · have h2 : (12 * r ≤ p ∧ p - 12 * r < k + 1) ↔ (12 * r ≤ p ∧ p - 12 * r < k) := by omega
      have h3 : (cond (b.testBit (12 * s + k)) (2 ^ (12 * r + k)) 0).testBit p = false := by
        cases b.testBit (12 * s + k) <;> simp [Ne.symm hp]
      rw [h3, Bool.false_xor]
      simp only [h2]

theorem colMv_eq_colUnit8 (a r s : ℕ) : colMv a r s = colUnit8 a r s 12 := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [testBit_colMv, testBit_colUnit8]
  have h : (s ≤ p ∧ p - s < 144 ∧ (p - s) % 12 = 0) ↔
      (s ≤ p ∧ (p - s) % 12 = 0 ∧ (p - s) / 12 < 12) := by omega
  simp only [h]

theorem rowMv_eq_rowUnit8 (b r s : ℕ) : rowMv b r s = rowUnit8 b r s 12 := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [testBit_rowMv, testBit_rowUnit8]

theorem linComb_colUnit8 {q : List ℕ} (hq : ∀ e ∈ q, e < 2 ^ 144) (a r s : ℕ) :
    ∀ k : ℕ, linComb q (colUnit8 a r s k) = colPk8 (packQ144 q) a r s k
  | 0 => by simp [colUnit8, colPk8, linComb_zero]
  | k + 1 => by
    rw [colUnit8, colPk8, isXorLin_linComb q, linComb_colUnit8 hq a r s k]
    cases a.testBit (12 * k + r) <;> simp [linComb_two_pow q hq, linComb_zero]

theorem linComb_rowUnit8 {q : List ℕ} (hq : ∀ e ∈ q, e < 2 ^ 144) (b r s : ℕ) :
    ∀ k : ℕ, linComb q (rowUnit8 b r s k) = rowPk8 (packQ144 q) b r s k
  | 0 => by simp [rowUnit8, rowPk8, linComb_zero]
  | k + 1 => by
    rw [rowUnit8, rowPk8, isXorLin_linComb q, linComb_rowUnit8 hq b r s k]
    cases b.testBit (12 * s + k) <;> simp [linComb_two_pow q hq, linComb_zero]

theorem conPartE_eq_P (r s : ℕ) : ∀ (cs : List (ℕ × ℕ)) (qs : List (List ℕ)),
    (∀ q ∈ qs, ∀ e ∈ q, e < 2 ^ 144) → conPartE cs qs r s = conPartP cs (qs.map packQ144) r s
  | c :: cs, q :: qs, h => by
    have hq := h q List.mem_cons_self
    rw [conPartE, List.map_cons, conPartP, isXorLin_linComb q, colMv_eq_colUnit8, rowMv_eq_rowUnit8,
      linComb_colUnit8 hq, linComb_rowUnit8 hq,
      conPartE_eq_P r s cs qs fun q' hq' => h q' (List.mem_cons_of_mem _ hq')]
  | [], _, _ => by simp [conPartE, conPartP]
  | _ :: _, [], _ => by simp [conPartE, conPartP]

theorem linCheckWith_of_P {cons : List (ℕ × ℕ)} {qc : List (List ℕ)} {qf fs : List ℕ}
    (h : linCheckP cons qc qf fs = true) : linCheckWith cons qc qf fs = true := by
  rw [linCheckP, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hb : ∀ q ∈ qc, ∀ e ∈ q, e < 2 ^ 144 := fun q hq e he => by
    rw [List.all_eq_true] at h1
    have h3 := h1 q hq
    rw [List.all_eq_true] at h3
    exact Nat.blt_eq.mp (h3 e he)
  have e : ∀ r s, conPartE cons qc r s = conPartP cons (qc.map packQ144) r s :=
    fun r s => conPartE_eq_P r s cons qc hb
  rw [linCheckWith_eq_E, linCheckE]
  simp only [e]
  exact h2

end CFSG.KC.O8

end
