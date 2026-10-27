module

public import CFSG.Certificates.Kernel.BabyMonster.Native.DyLane
public import CFSG.Certificates.Kernel.BabyMonster.DySound
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.BM.Ln

open CFSG.KC.BM CFSG.KC.BM.Dy

@[expose] def lay (x A B p : ℕ) : Bool := decide (p % B < A) && x.testBit (p / B * A + p % B)

theorem add_eq_or {a b : ℕ} (h : a &&& b = 0) : a + b = a ||| b := by
  have hab : a + b < 2 ^ (a + b) := Nat.lt_two_pow_self
  have ha : a < 2 ^ (a + b) := lt_of_le_of_lt (by omega) hab
  have hb : b < 2 ^ (a + b) := lt_of_le_of_lt (by omega) hab
  have h0 : BitVec.ofNat (a + b) a &&& BitVec.ofNat (a + b) b = 0#(a + b) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb, h, BitVec.toNat_zero]
  have key := congrArg BitVec.toNat (BitVec.add_eq_or_of_and_eq_zero _ _ h0)
  rw [BitVec.toNat_add, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hab] at key
  exact key

theorem testBit_add_of_and {a b : ℕ} (h : ∀ p, ¬(a.testBit p = true ∧ b.testBit p = true)) (p : ℕ) :
    (a + b).testBit p = (a.testBit p || b.testBit p) := by
  have h0 : a &&& b = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    have := h i
    cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all
  rw [add_eq_or h0, Nat.testBit_or]

theorem testBit_sub_and (y K p : ℕ) :
    (y - (y &&& K)).testBit p = (y.testBit p && !K.testBit p) := by
  have h1 : (y &&& K) &&& (y ^^^ (y &&& K)) = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
    cases y.testBit i <;> cases K.testBit i <;> decide
  have h2 : (y &&& K) ||| (y ^^^ (y &&& K)) = y := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
    cases y.testBit i <;> cases K.testBit i <;> decide
  have h3 := add_eq_or h1
  have e : y - (y &&& K) = y ^^^ (y &&& K) := by omega
  rw [e, Nat.testBit_xor, Nat.testBit_and]
  cases y.testBit p <;> cases K.testBit p <;> decide

theorem div_mod_of {p B k r : ℕ} (h : p = B * k + r) (hr : r < B) : p / B = k ∧ p % B = r :=
  (Nat.div_mod_unique (by omega)).2 ⟨by rw [h]; ring, hr⟩

theorem testBit_x_ge {x n i : ℕ} (hx : x < 2 ^ n) (hi : n ≤ i) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi))

theorem idx_ge {q N A r : ℕ} (h : N ≤ q) : 2 * A * N ≤ q * (2 * A) + r :=
  calc 2 * A * N = N * (2 * A) := by ring
    _ ≤ q * (2 * A) := Nat.mul_le_mul_right _ h
    _ ≤ _ := Nat.le_add_right _ _

theorem period_ge {p B N : ℕ} (hB : 0 < B) (h : ¬ p < 2 * B * N) : N ≤ p / (2 * B) := by
  by_contra hc
  have h1 := Nat.lt_mul_div_succ p (by omega : 0 < 2 * B)
  have h2 : 2 * B * (p / (2 * B) + 1) ≤ 2 * B * N := Nat.mul_le_mul_left _ (by omega)
  omega

theorem stage_lay {x A B N K y : ℕ} (hAB : A ≤ B) (hB : 0 < B)
    (hK : ∀ p, K.testBit p = (decide (p % (2 * B) < A) && decide (p < 2 * B * N)))
    (hx : x < 2 ^ (2 * A * N)) (hy : ∀ p, y.testBit p = lay x (2 * A) (2 * B) p) (p : ℕ) :
    (lnStage K (B - A) y).testBit p = lay x A B p := by
  have hst : lnStage K (B - A) y = (y &&& K) + ((y - (y &&& K)) <<< (B - A)) := rfl
  have hB2 : 0 < 2 * B := by omega
  have ha : ∀ p, (y &&& K).testBit p = (lay x (2 * A) (2 * B) p && K.testBit p) := fun p => by
    rw [Nat.testBit_and, hy]
  have hc : ∀ p, ((y - (y &&& K)) <<< (B - A)).testBit p =
      (decide (B - A ≤ p) && (lay x (2 * A) (2 * B) (p - (B - A)) && !K.testBit (p - (B - A)))) :=
    fun p => by rw [Nat.testBit_shiftLeft, testBit_sub_and, hy]
  have hcs : ∀ p, ((y - (y &&& K)) <<< (B - A)).testBit p = true →
      B ≤ p % (2 * B) ∧ p % (2 * B) < B + A := by
    intro p hp
    rw [hc] at hp
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hp
    obtain ⟨hD, hl, hk⟩ := hp
    unfold lay at hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
    obtain ⟨hl1, hl2⟩ := hl
    have hq := Nat.div_add_mod (p - (B - A)) (2 * B)
    have hs := Nat.mod_lt (p - (B - A)) hB2
    rw [hK] at hk
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt] at hk
    have hA' : A ≤ (p - (B - A)) % (2 * B) := by
      rcases hk with hk | hk
      · exact hk
      · exfalso
        have hN := period_ge hB (by omega : ¬ p - (B - A) < 2 * B * N)
        rw [testBit_x_ge hx (idx_ge hN)] at hl2
        exact absurd hl2 Bool.false_ne_true
    have e : p = 2 * B * ((p - (B - A)) / (2 * B)) + ((p - (B - A)) % (2 * B) + (B - A)) := by
      omega
    have e2 := (div_mod_of e (by omega)).2
    rw [e2]
    omega
  have has : ∀ p, (y &&& K).testBit p = true → p % (2 * B) < A := by
    intro p hp
    rw [ha, hK] at hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact hp.2.1
  rw [hst, testBit_add_of_and (fun p hp => by
    have h1 := has p hp.1
    have h2 := (hcs p hp.2).1
    omega)]
  have hq := Nat.div_add_mod p (2 * B)
  have hs : p % (2 * B) < 2 * B := Nat.mod_lt p hB2
  rcases Nat.lt_or_ge (p % (2 * B)) B with hsB | hsB
  ·
    have e : p = B * (2 * (p / (2 * B))) + p % (2 * B) := by
      calc p = 2 * B * (p / (2 * B)) + p % (2 * B) := hq.symm
        _ = _ := by ring
    obtain ⟨e1, e2⟩ := div_mod_of e hsB
    have hc0 : ((y - (y &&& K)) <<< (B - A)).testBit p = false := by
      cases h : ((y - (y &&& K)) <<< (B - A)).testBit p
      · rfl
      · have := (hcs p h).1
        omega
    rw [hc0, Bool.or_false, ha, hK]
    unfold lay
    rw [e1, e2]
    by_cases hsA : p % (2 * B) < A
    · have hsA2 : p % (2 * B) < 2 * A := by omega
      by_cases hpN : p < 2 * B * N
      · simp only [hsA, hsA2, hpN, decide_true, Bool.true_and, Bool.and_true]
        rw [show p / (2 * B) * (2 * A) + p % (2 * B) = 2 * (p / (2 * B)) * A + p % (2 * B) by ring]
      · have hqN := period_ge hB hpN
        simp only [hpN, decide_false, Bool.and_false]
        rw [testBit_x_ge hx (by
          calc 2 * A * N ≤ (p / (2 * B)) * (2 * A) + p % (2 * B) := idx_ge hqN
            _ = 2 * (p / (2 * B)) * A + p % (2 * B) := by ring)]
        simp
    · simp [hsA]
  ·
    obtain ⟨r, hr⟩ : ∃ r, p % (2 * B) = B + r := ⟨p % (2 * B) - B, by omega⟩
    have hrB : r < B := by omega
    have e : p = B * (2 * (p / (2 * B)) + 1) + r := by
      calc p = 2 * B * (p / (2 * B)) + p % (2 * B) := hq.symm
        _ = _ := by rw [hr]; ring
    obtain ⟨e1, e2⟩ := div_mod_of e hrB
    have ha0 : (y &&& K).testBit p = false := by
      cases h : (y &&& K).testBit p
      · rfl
      · have := has p h
        omega
    rw [ha0, Bool.false_or, hc]
    unfold lay
    rw [e1, e2]
    have hD : B - A ≤ p := by
      have : B ≤ p := by omega
      omega
    have e' : p - (B - A) = 2 * B * (p / (2 * B)) + (r + A) := by omega
    obtain ⟨f1, f2⟩ := div_mod_of e' (by omega : r + A < 2 * B)
    rw [hK, f1, f2]
    by_cases hrA : r < A
    · simp only [hD, hrA, decide_true, Bool.true_and, show r + A < 2 * A by omega,
        show ¬ r + A < A by omega, decide_false, Bool.false_and, Bool.not_false, Bool.and_true]
      rw [show p / (2 * B) * (2 * A) + (r + A) = (2 * (p / (2 * B)) + 1) * A + r by ring]
    · simp [hrA, show ¬ r + A < 2 * A by omega]

theorem geom (P : ℕ) (hP : 0 < P) (c : ℕ) :
    (2 ^ (P * (c + 1)) - 1) / (2 ^ P - 1) = 1 + 2 ^ P * ((2 ^ (P * c) - 1) / (2 ^ P - 1)) := by
  have h1 : 2 ≤ 2 ^ P := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ P := Nat.pow_le_pow_right (by decide) hP
  have hdvd : ∀ c : ℕ, ∃ g, 2 ^ (P * c) - 1 = (2 ^ P - 1) * g := by
    intro c
    induction c with
    | zero => exact ⟨0, by simp⟩
    | succ c ih =>
      obtain ⟨g, hg⟩ := ih
      have hp : 1 ≤ 2 ^ (P * c) := Nat.one_le_two_pow
      refine ⟨2 ^ P * g + 1, ?_⟩
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_add, Nat.mul_one, Nat.mul_left_comm, ← hg]
      have : 2 ^ (P * c) * 2 ^ P = 2 ^ P * (2 ^ (P * c) - 1) + 2 ^ P := by
        rw [Nat.mul_sub, Nat.mul_one, Nat.mul_comm]
        have : 2 ^ P ≤ 2 ^ P * 2 ^ (P * c) := Nat.le_mul_of_pos_right _ (by omega)
        omega
      omega
  obtain ⟨g, hg⟩ := hdvd c
  have hp : 1 ≤ 2 ^ (P * c) := Nat.one_le_two_pow
  have h3 : 2 ^ (P * (c + 1)) - 1 = (2 ^ P - 1) * (1 + 2 ^ P * g) := by
    rw [Nat.mul_succ, Nat.pow_add, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc,
      Nat.mul_comm (2 ^ P - 1) (2 ^ P), Nat.mul_assoc, ← hg]
    have : 2 ^ (P * c) * 2 ^ P = 2 ^ P * (2 ^ (P * c) - 1) + 2 ^ P := by
      rw [Nat.mul_sub, Nat.mul_one, Nat.mul_comm]
      have : 2 ^ P ≤ 2 ^ P * 2 ^ (P * c) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    omega
  have hpos : 0 < 2 ^ P - 1 := by omega
  rw [h3, hg, Nat.mul_div_cancel_left _ hpos, Nat.mul_div_cancel_left _ hpos]

theorem rep_succP (x P : ℕ) (hP : 0 < P) (c : ℕ) : rep x P (c + 1) = x + 2 ^ P * rep x P c := by
  rw [rep_eq, rep_eq, geom P hP, Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]

theorem rep_zeroP (x P : ℕ) : rep x P 0 = 0 := by
  rw [rep_eq]
  simp

theorem testBit_rep_ones {L P : ℕ} (hLP : L ≤ P) (hP : 0 < P) :
    ∀ (c p : ℕ), (rep (2 ^ L - 1) P c).testBit p = (decide (p % P < L) && decide (p < P * c))
  | 0, p => by simp [rep_zeroP]
  | c + 1, p => by
    have hlt : 2 ^ L - 1 < 2 ^ P :=
      lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos L) (by decide)) (Nat.pow_le_pow_right (by decide) hLP)
    rw [rep_succP _ _ hP, Nat.add_comm, Nat.testBit_two_pow_mul_add _ hlt]
    split
    · rename_i hp
      rw [Nat.testBit_two_pow_sub_one, Nat.mod_eq_of_lt hp]
      simp only [show p < P * (c + 1) by
        calc p < P := hp
          _ ≤ P * (c + 1) := Nat.le_mul_of_pos_right _ (by omega), decide_true, Bool.and_true]
    · rename_i hp
      rw [testBit_rep_ones hLP hP c (p - P)]
      have e : p = P * 1 + (p - P) := by omega
      have e1 : (p - P) % P = p % P := by
        conv_rhs => rw [e]
        rw [Nat.mul_add_mod]
      rw [e1]
      congr 2
      apply propext
      constructor
      · intro h
        rw [Nat.mul_succ]
        omega
      · intro h
        rw [Nat.mul_succ] at h
        omega

theorem shl_one (n : ℕ) : Nat.shiftLeft (nat_lit 1) n = 2 ^ n := by
  rw [Nat.shiftLeft_eq', Nat.one_shiftLeft]

theorem testBit_lnK {w W : ℕ} (hwW : w ≤ W) (hW : 0 < W) (b p : ℕ) :
    (lnK w W b).testBit p =
      (decide (p % (W * 2 ^ (b + 1)) < w * 2 ^ b) && decide (p < W * 2 ^ (b + 1) * 2 ^ (12 - b))) := by
  have e : lnK w W b = rep (2 ^ (w * 2 ^ b) - 1) (W * 2 ^ (b + 1)) (2 ^ (12 - b)) := by
    unfold lnK onesN
    rw [shl_one, shl_one, shl_one, shl_one]
    rfl
  rw [e]
  exact testBit_rep_ones (by
    calc w * 2 ^ b ≤ W * 2 ^ b := Nat.mul_le_mul_right _ hwW
      _ ≤ W * 2 ^ (b + 1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega)))
    (Nat.mul_pos hW (Nat.two_pow_pos _)) _ p

@[expose] noncomputable def ksFrom (w W c : ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => List Nat) List.nil (fun b acc => List.cons (lnK w W b) acc) c

theorem lnSpr_cons (K : ℕ) (Ks : List ℕ) (D x : ℕ) :
    lnSpr (K :: Ks) D x = lnSpr Ks (D >>> 1) (lnStage K D x) := by
  change forceB (lnStage K D x) (fun x' => lnSpr Ks (Nat.shiftRight D (nat_lit 1)) x') = _
  rw [forceB_apply]
  rfl

theorem spr_chain {x w W : ℕ} (hwW : w ≤ W) (hw : 0 < w) (hx : x < 2 ^ (8192 * w)) :
    ∀ c ≤ 13, ∀ y D, (∀ p, y.testBit p = lay x (w * 2 ^ c) (W * 2 ^ c) p) →
      (1 ≤ c → D = (W - w) * 2 ^ (c - 1)) →
      ∀ p, (lnSpr (ksFrom w W c) D y).testBit p = lay x w W p
  | 0, _, y, D, hy, _, p => by
    have e : lnSpr (ksFrom w W 0) D y = y := rfl
    rw [e, hy]
    simp
  | c + 1, hc, y, D, hy, hD, p => by
    have e : ksFrom w W (c + 1) = lnK w W c :: ksFrom w W c := rfl
    rw [e, lnSpr_cons]
    have hW : 0 < W := by omega
    have hB : 0 < W * 2 ^ c := Nat.mul_pos hW (Nat.two_pow_pos c)
    have hD' : D = W * 2 ^ c - w * 2 ^ c := by
      rw [hD (by omega), Nat.add_sub_cancel, Nat.sub_mul]
    refine spr_chain hwW hw hx c (by omega) _ _ (fun p => ?_) (fun hc1 => ?_) p
    · rw [hD']
      refine stage_lay (N := 2 ^ (12 - c)) (Nat.mul_le_mul_right _ hwW) hB (fun p => ?_) ?_
        (fun p => ?_) p
      · rw [testBit_lnK hwW hW, show 2 * (W * 2 ^ c) = W * 2 ^ (c + 1) by ring]
      · have e2 : 2 * (w * 2 ^ c) * 2 ^ (12 - c) = 8192 * w := by
          rw [show 2 * (w * 2 ^ c) * 2 ^ (12 - c) = w * (2 ^ (c + 1) * 2 ^ (12 - c)) by ring,
            ← Nat.pow_add, show c + 1 + (12 - c) = 13 by omega]
          ring
        rw [e2]
        exact hx
      · rw [hy, show w * 2 ^ (c + 1) = 2 * (w * 2 ^ c) by ring,
          show W * 2 ^ (c + 1) = 2 * (W * 2 ^ c) by ring]
    · rw [hD (by omega), Nat.add_sub_cancel, Nat.shiftRight_eq_div_pow, pow_one]
      obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by decide), Nat.add_sub_cancel]

theorem testBit_spr {x w W : ℕ} (hwW : w ≤ W) (hw : 0 < w) (hx : x < 2 ^ (8192 * w)) (p : ℕ) :
    (lnSpr (lnKs w W) (lnD w W) x).testBit p = lay x w W p := by
  have e : lnKs w W = ksFrom w W 13 := rfl
  have eD : lnD w W = (W - w) * 2 ^ (13 - 1) := rfl
  rw [e, eD]
  refine spr_chain hwW hw hx 13 le_rfl x _ (fun p => ?_) (fun _ => rfl) p
  unfold lay
  have hW : 0 < W * 2 ^ 13 := Nat.mul_pos (by omega) (Nat.two_pow_pos 13)
  rcases Nat.lt_or_ge p (W * 2 ^ 13) with hp | hp
  · rw [Nat.div_eq_of_lt hp, Nat.mod_eq_of_lt hp, Nat.zero_mul, Nat.zero_add]
    by_cases h : p < w * 2 ^ 13
    · rw [decide_eq_true h, Bool.true_and]
    · rw [testBit_x_ge hx (by omega), decide_eq_false h, Bool.false_and]
  · rw [testBit_x_ge hx (by omega)]
    have h1 : 1 ≤ p / (W * 2 ^ 13) := (Nat.le_div_iff_mul_le hW).2 (by omega)
    rw [testBit_x_ge hx (by
      calc 8192 * w = 1 * (w * 2 ^ 13) := by ring
        _ ≤ p / (W * 2 ^ 13) * (w * 2 ^ 13) := Nat.mul_le_mul_right _ h1
        _ ≤ _ := Nat.le_add_right _ _)]
    simp

end CFSG.KC.BM.Ln

end
