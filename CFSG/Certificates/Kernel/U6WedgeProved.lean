module

import CFSG.Certificates.Kernel.U6LinProved
public import CFSG.Certificates.Kernel.U6LinSound
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDWedgeData
public import Certificates.Data.Kernel.U6.WedgeK
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.KC.U6F2

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2
open CFSG.EvenSmallLie.UnitarySix.YamadaPar (toMat bmul bIsId xorFold xorFold_succ testBit_rowMul)

private theorem bmul_row_bitW {n k i j : ℕ} (A B : Array ℕ) (hi : i < n) :
    ((bmul n k A B).getD i 0).testBit j =
      xorFold k fun l => (A.getD i 0).testBit l && (B.getD l 0).testBit j := by
  simp only [bmul, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hi, ↓reduceDIte,
    Option.getD_some]
  rw [testBit_rowMul]
  simp only [Array.getD_eq_getD_getElem?]

private theorem getD_toListW (A : Array ℕ) (t : ℕ) : A.toList.getD t 0 = A.getD t 0 := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]

private theorem xorFold_congrW {k : ℕ} {f g : ℕ → Bool} (h : ∀ l < k, f l = g l) :
    xorFold k f = xorFold k g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [xorFold_succ, xorFold_succ, ih (fun l hl => h l (by omega)), h k (by omega)]

theorem bIsId_bmul_of_idRowsK_proved {N P : ℕ} {Q R : Array ℕ} {RL : List ℕ}
    (hR : R.toList = RL) (hP : RL.length = P)
    (h : idRowsK N Q.toList (List.replicate N 0) [] RL = true) :
    bIsId N (bmul N P Q R) = true := by
  obtain ⟨_, _, hb⟩ := idRowsK_bit_proved h
  simp only [bIsId, List.all_eq_true, List.mem_range, beq_iff_eq]
  intro i hi j hj
  have := hb i hi j hj
  have hx0 : ∀ g : ℕ → Bool, xorFold ([] : List ℕ).length g = false := fun _ => rfl
  rw [hx0, Bool.false_xor, hP] at this
  rw [bmul_row_bitW _ _ hi, ← this]
  apply xorFold_congrW
  intro l _
  rw [getD_toListW, ← hR, getD_toListW]

private theorem xorFold_succW' (f : ℕ → Bool) : ∀ k,
    xorFold (k + 1) f = (f 0 ^^ xorFold k fun t => f (t + 1))
  | 0 => by simp [xorFold]
  | k + 1 => by
    rw [xorFold_succ, xorFold_succW' f k, xorFold_succ]
    cases f 0 <;> cases xorFold k (fun t => f (t + 1)) <;> cases f (k + 1) <;> rfl

private theorem xorFold_falseW : ∀ k, xorFold k (fun _ => false) = false
  | 0 => rfl
  | k + 1 => by rw [xorFold_succ, xorFold_falseW k]; rfl

private theorem bit_eqW (X i : ℕ) : bit X i = X.testBit i := by
  have e : bit X i = Nat.beq ((X >>> i) % 2) 1 := by
    change Nat.beq ((X >>> i) &&& 1) 1 = _
    rw [Nat.and_one_is_mod]
  have h2 : X.testBit i = decide ((X >>> i) % 2 = 1) := by
    rw [← Nat.testBit_zero, Nat.testBit_shiftRight, Nat.add_zero]
  rw [e, h2]
  rcases Nat.mod_two_eq_zero_or_one (X >>> i) with h | h <;> rw [h] <;> rfl

private noncomputable def rzAux (B : List ℕ) : ℕ → ℕ → ℕ :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun b _ ih a acc => nIf(Nat.beq a 0, acc,
      strictN (nIf(bit a (nat_lit 0), Nat.xor acc b, acc)) fun acc =>
        ih (Nat.shiftRight a (nat_lit 1)) acc)) B

private theorem testBit_rzAux (q : ℕ) : ∀ (B : List ℕ) (a acc : ℕ),
    (rzAux B a acc).testBit q =
      (acc.testBit q ^^ xorFold B.length fun t => a.testBit t && (B.getD t 0).testBit q)
  | [], a, acc => by simp [rzAux, xorFold]
  | b :: B, a, acc => by
    by_cases ha : a = 0
    · subst ha
      have e : rzAux (b :: B) 0 acc = acc := rfl
      rw [e]
      have : (xorFold (b :: B).length fun t => (0 : ℕ).testBit t && ((b :: B).getD t 0).testBit q) =
          xorFold (b :: B).length (fun _ => false) := by
        apply xorFold_congrW
        intro l _
        simp
      rw [this, xorFold_falseW]
      simp
    · have hb : Nat.beq a 0 = false := by
        cases e : Nat.beq a 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) ha
      have e : rzAux (b :: B) a acc =
          rzAux B (a >>> 1) (Bool.rec (motive := fun _ => ℕ) acc (Nat.xor acc b) (bit a 0)) := by
        change Bool.rec (motive := fun _ => ℕ) (strictN _ _) acc (Nat.beq a 0) = _
        rw [hb]
        change strictN _ _ = _
        rw [strictN_eq]
        rfl
      rw [e, testBit_rzAux q B, List.length_cons, xorFold_succW']
      simp only [Nat.testBit_shiftRight, List.getD_cons_succ, List.getD_cons_zero, bit_eqW]
      have e2 : ∀ t, a.testBit (1 + t) = a.testBit (t + 1) := fun t => by rw [Nat.add_comm]
      simp only [e2]
      cases a.testBit 0
      · simp
      · change ((acc ^^^ b).testBit q ^^ _) = _
        rw [Nat.testBit_xor]
        simp

private theorem testBit_fgetW (X i w p : ℕ) :
    (fget X i w).testBit p = (decide (p < w) && X.testBit (i * w + p)) := by
  change ((X >>> (i * w)) &&& maskN w).testBit p = _
  have e : maskN w = 2 ^ w - 1 := by
    rw [maskN]
    change Nat.sub (1 <<< w) 1 = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    rfl
  rw [e, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem bIsId_bmul_of_blocks_proved {k P : ℕ} {Q R : Array ℕ} {RL : List ℕ} (hR : R.toList = RL)
    (hP : RL.length = P) (h : ∀ c < k, blockRowsK (64 * k) c Q.toList RL = true) :
    bIsId (64 * k) (bmul (64 * k) P Q R) = true := by
  simp only [bIsId, List.all_eq_true, List.mem_range, beq_iff_eq]
  intro i hi j hj
  have hc : j / 64 < k := by omega
  have hq : j % 64 < 64 := Nat.mod_lt _ (by decide)
  have hj' : j / 64 * 64 + j % 64 = j := by omega
  have hb := h (j / 64) hc
  simp only [blockRowsK, List.all_eq_true, List.mem_range] at hb
  have hrow := Nat.eq_of_beq_eq_true (hb i hi)
  have hbit := congrArg (fun x => x.testBit (j % 64)) hrow
  have e1 : rowMulZ (getLD 0 Q.toList i) (RL.map fun r => fget r (j / 64) 64) =
      rzAux (RL.map fun r => fget r (j / 64) 64) (getLD 0 Q.toList i) 0 := rfl
  rw [e1, testBit_rzAux, testBit_fgetW, hj'] at hbit
  have e2 : pw2 i = 2 ^ i := Nat.one_shiftLeft i
  rw [e2, Nat.testBit_two_pow] at hbit
  simp only [Nat.zero_testBit, Bool.false_xor, List.length_map, hq, decide_true,
    Bool.true_and] at hbit
  rw [bmul_row_bitW _ _ (by omega), ← hP, ← hbit]
  apply xorFold_congrW
  intro l hl
  rw [getLD_eq_getD, getD_toListW Q i, ← hR]
  have hl' : l < R.size := by
    rw [← hR] at hl
    simpa using hl
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
    Array.getElem?_eq_getElem hl', Option.map_some, Option.getD_some, testBit_fgetW, hj']
  simp [hq, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hl']

open CFSG.EvenSmallLie.UnitarySix.YamadaD (wedgeEq wedgeEqP eCol eRow WRow WCol)
open CFSG.EvenSmallLie.UnitarySix.YamadaPar (bz matBits testBit_bitsOf toMat_apply)

private theorem eCol_val {n : ℕ} (k l s : Fin n) :
    ((eCol n) (k, l, s) : ℕ) = s + n * l + n * n * k := by
  simp [eCol, finProdFinEquiv]

private theorem eRow_inl_val {n m : ℕ} (g : Fin m) (k l s : Fin n) :
    ((eRow n m) (Sum.inl (g, k, l, s)) : ℕ) = (s + n * l + n * n * k) + n * (n * n) * g := by
  simp [eRow, eCol, finProdFinEquiv, finSumFinEquiv_apply_left]

private theorem eRow_inr_val {n m : ℕ} (k l s : Fin n) :
    ((eRow n m) (Sum.inr (k, l, s)) : ℕ) = m * (n * (n * n)) + (s + n * l + n * n * k) := by
  simp [eRow, eCol, finProdFinEquiv, finSumFinEquiv_apply_right]

private theorem digits3 {n x : ℕ} (hx : x < n * (n * n)) :
    x % n + n * (x / n % n) + n * n * (x / (n * n)) = x ∧ x % n < n ∧ x / n % n < n ∧
      x / (n * n) < n := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp at hx
    · exact h
  refine ⟨?_, Nat.mod_lt _ hn, Nat.mod_lt _ hn, ?_⟩
  · have h1 := Nat.div_add_mod x n
    have h2 := Nat.div_add_mod (x / n) n
    have h3 : x / n / n = x / (n * n) := Nat.div_div_eq_div_mul x n n
    rw [h3] at h2
    calc x % n + n * (x / n % n) + n * n * (x / (n * n))
        = x % n + n * (n * (x / (n * n)) + x / n % n) := by ring
      _ = x := by rw [h2, Nat.add_comm, h1]
  · apply Nat.div_lt_of_lt_mul
    rw [Nat.mul_comm (n * n) n]
    exact hx

private theorem digits3_unique {n a b c a' b' c' : ℕ} (ha : a < n) (hb : b < n) (ha' : a' < n)
    (hb' : b' < n) (h : a + n * b + n * n * c = a' + n * b' + n * n * c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have hn : 0 < n := by omega
  have e1 : (a + n * b + n * n * c) % n = a := by
    rw [Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  have e1' : (a' + n * b' + n * n * c') % n = a' := by
    rw [Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt ha']
  have f1 : (a + n * b + n * n * c) / n = b + n * c := by
    rw [Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add, Nat.add_mul_div_left _ _ hn,
      Nat.div_eq_of_lt ha, Nat.zero_add]
  have f1' : (a' + n * b' + n * n * c') / n = b' + n * c' := by
    rw [Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add, Nat.add_mul_div_left _ _ hn,
      Nat.div_eq_of_lt ha', Nat.zero_add]
  have g1 : (b + n * c) % n = b := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  have g1' : (b' + n * c') % n = b' := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb']
  have k1 : (b + n * c) / n = c := by
    rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hb, Nat.zero_add]
  have k1' : (b' + n * c') / n = c' := by
    rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hb', Nat.zero_add]
  refine ⟨by rw [← e1, ← e1', h], ?_, ?_⟩
  · rw [← g1, ← g1', ← f1, ← f1', h]
  · rw [← k1, ← k1', ← f1, ← f1', h]

private theorem digits3_lt {n a b c : ℕ} (ha : a < n) (hb : b < n) (hc : c < n) :
    a + n * b + n * n * c < n * (n * n) := by
  have h1 : a + n * b < n * n := by
    have : n * b + n ≤ n * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hb
    omega
  have h2 : n * n * c + n * n ≤ n * (n * n) := by
    rw [← Nat.mul_succ, Nat.mul_comm n (n * n)]
    exact Nat.mul_le_mul_left _ hc
  omega

private theorem testBit_orN_anyW (f : ℕ → ℕ) (p : ℕ) : ∀ n,
    (orN n f).testBit p = (List.range n).any fun i => (f i).testBit p
  | 0 => by
    have e : orN 0 f = 0 := rfl
    rw [e]
    simp
  | n + 1 => by
    have e : orN (n + 1) f = f n ||| orN n f := rfl
    rw [e, Nat.testBit_or, testBit_orN_anyW f p n, List.range_succ, List.any_append]
    simp [Bool.or_comm]

private theorem testBit_nIfW (c : Bool) (x y t : ℕ) :
    (Bool.rec (motive := fun _ => ℕ) y x c).testBit t = (if c then x.testBit t else y.testBit t) := by
  cases c <;> rfl

private theorem pw2_eqW (w : ℕ) : pw2 w = 2 ^ w := Nat.one_shiftLeft w

private theorem bit_packMW {n a b : ℕ} (A : Array ℕ) (ha : a < n) (hb : b < n) :
    bit (packM n A) (n * a + b) = (A.getD a 0).testBit b := by
  rw [bit_eqW, testBit_packM]
  have h1 : n * a + b < n * n := by
    have : n * a + n ≤ n * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ ha
    omega
  have e1 : (n * a + b) / n = a := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hb, Nat.zero_add]
  have e2 : (n * a + b) % n = b := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  simp [h1, e1, e2]

private theorem testBit_wEqA {n i j r c : ℕ} (A : Array ℕ) (hi : i < n) (hj : j < n) (hr : r < n) :
    (orN n fun k => Bool.rec (motive := fun _ => ℕ) 0 (orN n fun l =>
        Bool.rec (motive := fun _ => ℕ) 0
          (pw2 (Nat.add r (Nat.add (Nat.mul n l) (Nat.mul (Nat.mul n n) k))))
          (bit (packM n A) (Nat.add (Nat.mul n l) j)))
      (bit (packM n A) (Nat.add (Nat.mul n k) i))).testBit c =
      (decide (c < n * (n * n)) && (decide (c % n = r) &&
        ((A.getD (c / (n * n)) 0).testBit i && (A.getD (c / n % n) 0).testBit j))) := by
  rw [testBit_orN_anyW]
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_range, testBit_nIfW, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨k, hk, h⟩
    split at h
    · rename_i hbk
      rw [testBit_orN_anyW] at h
      simp only [List.any_eq_true, List.mem_range, testBit_nIfW] at h
      obtain ⟨l, hl, h⟩ := h
      split at h
      · rename_i hbl
        rw [pw2_eqW, Nat.testBit_two_pow] at h
        have hc : r + n * l + n * n * k = c := by simpa [Nat.add_assoc] using h
        subst hc
        have hlt := digits3_lt hr hl hk
        obtain ⟨d1, d2, d3, d4⟩ := digits3 hlt
        obtain ⟨u1, u2, u3⟩ := digits3_unique d2 d3 hr hl d1
        rw [u2, u3]
        refine ⟨hlt, u1, ?_, ?_⟩
        · rwa [Nat.mul_eq, Nat.add_eq, bit_packMW A hk hi] at hbk
        · rwa [Nat.mul_eq, Nat.add_eq, bit_packMW A hl hj] at hbl
      · simp at h
    · simp at h
  · rintro ⟨hc, hcr, hbi, hbj⟩
    obtain ⟨d1, d2, d3, d4⟩ := digits3 hc
    refine ⟨c / (n * n), d4, ?_⟩
    have hbk : bit (packM n A) (Nat.add (Nat.mul n (c / (n * n))) i) = true := by
      rw [Nat.mul_eq, Nat.add_eq, bit_packMW A d4 hi]
      exact hbi
    rw [hbk, ite_eq_left rfl, testBit_orN_anyW]
    simp only [List.any_eq_true, List.mem_range, testBit_nIfW]
    refine ⟨c / n % n, d3, ?_⟩
    have hbl : bit (packM n A) (Nat.add (Nat.mul n (c / n % n)) j) = true := by
      rw [Nat.mul_eq, Nat.add_eq, bit_packMW A d3 hj]
      exact hbj
    rw [hbl, ite_eq_left rfl, pw2_eqW, Nat.testBit_two_pow]
    simp only [decide_eq_true_eq, Nat.add_eq, Nat.mul_eq]
    rw [← hcr] at *
    omega

private theorem testBit_wEqB {n i j r c : ℕ} (A : Array ℕ) (hi : i < n) (hj : j < n) (hr : r < n) :
    (orN n fun s => Bool.rec (motive := fun _ => ℕ) 0
        (pw2 (Nat.add s (Nat.add (Nat.mul n j) (Nat.mul (Nat.mul n n) i))))
        (bit (packM n A) (Nat.add (Nat.mul n r) s))).testBit c =
      (decide (c < n * (n * n)) && (decide (c / (n * n) = i ∧ c / n % n = j) &&
        (A.getD r 0).testBit (c % n))) := by
  rw [testBit_orN_anyW]
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_range, testBit_nIfW, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨s, hs, h⟩
    split at h
    · rename_i hbs
      rw [pw2_eqW, Nat.testBit_two_pow] at h
      have hc : s + n * j + n * n * i = c := by simpa [Nat.add_assoc] using h
      subst hc
      have hlt := digits3_lt hs hj hi
      obtain ⟨d1, d2, d3, d4⟩ := digits3 hlt
      obtain ⟨u1, u2, u3⟩ := digits3_unique d2 d3 hs hj d1
      rw [u1, u2, u3]
      refine ⟨hlt, ⟨rfl, rfl⟩, ?_⟩
      rwa [Nat.mul_eq, Nat.add_eq, bit_packMW A hr hs] at hbs
    · simp at h
  · rintro ⟨hc, ⟨hci, hcj⟩, hb⟩
    obtain ⟨d1, d2, d3, d4⟩ := digits3 hc
    refine ⟨c % n, d2, ?_⟩
    have hbs : bit (packM n A) (Nat.add (Nat.mul n r) (c % n)) = true := by
      rw [Nat.mul_eq, Nat.add_eq, bit_packMW A hr d2]
      exact hb
    rw [hbs, ite_eq_left rfl, pw2_eqW, Nat.testBit_two_pow]
    simp only [decide_eq_true_eq, Nat.add_eq, Nat.mul_eq]
    rw [← hci, ← hcj]
    omega

private theorem testBit_wAlt {n k l s c : ℕ} (hk : k < n) (hl : l < n) (hs : s < n) :
    (wAltRow n k l s).testBit c =
      (decide (c < n * (n * n)) && (decide (c % n = s) &&
        ((decide (c / (n * n) = k) && decide (c / n % n = l)) ||
          (decide (c / (n * n) = l) && decide (c / n % n = k))))) := by
  change (pw2 (s + (n * l + n * n * k)) ||| pw2 (s + (n * k + n * n * l))).testBit c = _
  rw [Nat.testBit_or, pw2_eqW, pw2_eqW, Nat.testBit_two_pow, Nat.testBit_two_pow]
  apply Bool.eq_iff_iff.2
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · rintro (h | h)
    · have hc : s + n * l + n * n * k = c := by rw [← h]; ring
      subst hc
      have hlt := digits3_lt hs hl hk
      obtain ⟨d1, d2, d3, d4⟩ := digits3 hlt
      obtain ⟨u1, u2, u3⟩ := digits3_unique d2 d3 hs hl d1
      exact ⟨hlt, u1, Or.inl ⟨u3, u2⟩⟩
    · have hc : s + n * k + n * n * l = c := by rw [← h]; ring
      subst hc
      have hlt := digits3_lt hs hk hl
      obtain ⟨d1, d2, d3, d4⟩ := digits3 hlt
      obtain ⟨u1, u2, u3⟩ := digits3_unique d2 d3 hs hk d1
      exact ⟨hlt, u1, Or.inr ⟨u3, u2⟩⟩
  · rintro ⟨hc, hcs, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
    · obtain ⟨d1, _, _, _⟩ := digits3 hc
      left
      rw [← hcs, ← h1, ← h2]
      calc c % n + (n * (c / n % n) + n * n * (c / (n * n)))
          = c % n + n * (c / n % n) + n * n * (c / (n * n)) := by ring
        _ = c := d1
    · obtain ⟨d1, _, _, _⟩ := digits3 hc
      right
      rw [← hcs, ← h1, ← h2]
      calc c % n + (n * (c / n % n) + n * n * (c / (n * n)))
          = c % n + n * (c / n % n) + n * n * (c / (n * n)) := by ring
        _ = c := d1

private theorem entry_beq (p q : Prop) [Decidable p] [Decidable q] (a b c : Bool) :
    ((if p then bz a * bz b else 0) + (if q then bz c else 0) == (1 : ZMod 2)) =
      ((decide p && (a && b)) ^^ (decide q && c)) := by
  by_cases hp : p <;> by_cases hq : q <;> cases a <;> cases b <;> cases c <;>
    simp [hp, hq, bz]

private theorem alt_beq (p : Prop) [Decidable p] :
    ((if p then (1 : ZMod 2) else 0) == 1) = decide p := by
  by_cases hp : p <;> simp [hp]

private theorem blt_tW {a b : ℕ} (h : a < b) : Nat.blt a b = true := by simpa using h

private theorem blt_fW {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases e : Nat.blt a b
  · rfl
  · exact absurd (by simpa using e) h

private theorem wRowK_inl {n m ρ : ℕ} (GP : List ℕ) (hr : ρ < m * (n * (n * n))) :
    wRowK n m GP ρ = wEqRow n (getLD 0 GP (ρ / (n * (n * n)))) (ρ % (n * (n * n)) / (n * n))
      (ρ % (n * (n * n)) / n % n) (ρ % (n * (n * n)) % n) := by
  unfold wRowK
  simp only [Nat.mul_eq, blt_tW hr]
  rfl

private theorem wRowK_inr {n m ρ : ℕ} (GP : List ℕ) (hr : ¬ ρ < m * (n * (n * n))) :
    wRowK n m GP ρ = wAltRow n ((ρ - m * (n * (n * n))) / (n * n))
      ((ρ - m * (n * (n * n))) / n % n) ((ρ - m * (n * (n * n))) % n) := by
  unfold wRowK
  simp only [Nat.mul_eq, blt_fW hr]
  rfl

theorem wedgeR_toList_proved{n m : ℕ} (G : Fin m → Array ℕ) {GP : List ℕ}
    (hG : ∀ g : Fin m, getLD 0 GP g.val = packM n (G g)) :
    (CFSG.EvenSmallLie.UnitarySix.YamadaD.wedgeR fun g => toMat n n (G g)).toList =
      wedgeRK n m GP := by
  apply List.ext_getElem
  · simp [CFSG.EvenSmallLie.UnitarySix.YamadaD.wedgeR, matBits, wedgeRK]
  intro ρ h1 h2
  have hρ : ρ < m * (n * (n * n)) + n * (n * n) := by
    simpa [CFSG.EvenSmallLie.UnitarySix.YamadaD.wedgeR, matBits] using h1
  simp only [CFSG.EvenSmallLie.UnitarySix.YamadaD.wedgeR, matBits, Array.toList_ofFn,
    List.getElem_ofFn, wedgeRK, List.getElem_map, List.getElem_range]
  apply Nat.eq_of_testBit_eq
  intro c
  rw [testBit_bitsOf]
  by_cases hr : ρ < m * (n * (n * n))
  · have hn3 : 0 < n * (n * n) := by
      rcases Nat.eq_zero_or_pos (n * (n * n)) with h | h
      · rw [h] at hr
        simp at hr
      · exact h
    have hg : ρ / (n * (n * n)) < m := by
      rw [Nat.div_lt_iff_lt_mul hn3]
      exact hr
    obtain ⟨x1, x2, x3, x4⟩ := digits3 (Nat.mod_lt ρ hn3)
    have hrow : (eRow n m).symm ⟨ρ, by omega⟩ = Sum.inl (⟨ρ / (n * (n * n)), hg⟩,
        ⟨ρ % (n * (n * n)) / (n * n), x4⟩, ⟨ρ % (n * (n * n)) / n % n, x3⟩,
        ⟨ρ % (n * (n * n)) % n, x2⟩) := by
      rw [Equiv.symm_apply_eq]
      apply Fin.ext
      rw [eRow_inl_val]
      simp only
      rw [x1]
      exact (Nat.mod_add_div ρ _).symm
    rw [wRowK_inl GP hr, hG ⟨_, hg⟩]
    unfold wEqRow
    change _ = Nat.testBit (HXor.hXor (α := ℕ) (β := ℕ) _ _) c
    rw [Nat.testBit_xor, testBit_wEqA _ x4 x3 x2, testBit_wEqB _ x4 x3 x2]
    by_cases hc : c < n * (n * n)
    · obtain ⟨d1, d2, d3, d4⟩ := digits3 hc
      have hcol : (eCol n).symm ⟨c, hc⟩ = (⟨c / (n * n), d4⟩, ⟨c / n % n, d3⟩, ⟨c % n, d2⟩) := by
        rw [Equiv.symm_apply_eq]
        apply Fin.ext
        rw [eCol_val]
        exact d1.symm
      simp only [hc, decide_true, Bool.true_and, ↓reduceDIte, wedgeEq, Matrix.reindex_apply,
        Matrix.submatrix_apply, hrow, hcol, wedgeEqP, toMat_apply]
      rw [entry_beq]
      simp only [Fin.mk.injEq]
    · simp [hc]
  · have hn3' : ρ - m * (n * (n * n)) < n * (n * n) := by omega
    obtain ⟨x1, x2, x3, x4⟩ := digits3 hn3'
    have hrow : (eRow n m).symm ⟨ρ, by omega⟩ = Sum.inr
        (⟨(ρ - m * (n * (n * n))) / (n * n), x4⟩, ⟨(ρ - m * (n * (n * n))) / n % n, x3⟩,
          ⟨(ρ - m * (n * (n * n))) % n, x2⟩) := by
      rw [Equiv.symm_apply_eq]
      apply Fin.ext
      rw [eRow_inr_val]
      simp only
      rw [x1]
      omega
    rw [wRowK_inr GP hr, testBit_wAlt x4 x3 x2]
    by_cases hc : c < n * (n * n)
    · obtain ⟨d1, d2, d3, d4⟩ := digits3 hc
      have hcol : (eCol n).symm ⟨c, hc⟩ = (⟨c / (n * n), d4⟩, ⟨c / n % n, d3⟩, ⟨c % n, d2⟩) := by
        rw [Equiv.symm_apply_eq]
        apply Fin.ext
        rw [eCol_val]
        exact d1.symm
      simp only [hc, decide_true, Bool.true_and, ↓reduceDIte, wedgeEq, Matrix.reindex_apply,
        Matrix.submatrix_apply, hrow, hcol, wedgeEqP]
      rw [alt_beq]
      simp only [Fin.mk.injEq, Bool.decide_and, Bool.decide_or]
    · simp [hc]

open CFSG.EvenSmallLie.UnitarySix.YamadaD (wedgeR)

end CFSG.KC.U6F2

end
