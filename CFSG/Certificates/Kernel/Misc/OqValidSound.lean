module

public import Certificates.Data.Kernel.Misc.Oq
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneOqInputs
import Mathlib.Tactic.IntervalCases
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneOqDataKill
public import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.KC.Misc.Oq

open CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc
open CFSG.EvenSmallLie.OmegaEight.SpBranch (xorBits xorBits_succ xorBits_lt)

private theorem andB_iff {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> simp [andB]

private theorem orB_iff {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp [orB]

private theorem notB_iff {a : Bool} : notB a = true ↔ a = false := by
  cases a <;> simp [notB]

private theorem allN_iff' {m : ℕ} {f : ℕ → Bool} : allN m f = true ↔ ∀ i, i < m → f i = true := by
  induction m with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ m ih =>
    change andB (f m) (allN m f) = true ↔ _
    rw [andB_iff, ih, Nat.forall_lt_succ_right, and_comm]

private theorem letB_eq' (y : ℕ) (k : ℕ → Bool) : letB y k = k y := by cases y <;> rfl

private theorem nbeq_iff (a b : ℕ) : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl _⟩

private theorem fld6_eq (P i : ℕ) : fld6 P i = P / 64 ^ i % 64 := by
  have h : fld6 P i = (P >>> (6 * i)) &&& (2 ^ 6 - 1) := rfl
  rw [h, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

private theorem fld6_lt (P i : ℕ) : fld6 P i < 64 := by
  rw [fld6_eq]; exact Nat.mod_lt _ (by norm_num)

private theorem getD_unpack6 {P j : ℕ} (hj : j < 6) : (unpack6 P).getD j 0 = fld6 P j := by
  simp [unpack6, fld6_eq, List.getD_eq_getElem?_getD, hj]

private theorem bit_eq (v j : ℕ) : bit v j = if v.testBit j then 1 else 0 := by
  have h : bit v j = (v >>> j) &&& 1 := rfl
  rw [h, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ j) with h | h <;> simp [h]

private theorem mul_bit (a k x : ℕ) : Nat.mul (bit a k) x = if a.testBit k then x else 0 := by
  rw [bit_eq]; split_ifs <;> simp

private theorem rec_xor_eq (F : ℕ → ℕ) (e n : ℕ) :
    (Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => Nat.xor acc (Nat.mul (bit e k) (F k))) n : ℕ) =
      xorBits n F e := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [xorBits_succ, ← ih]
    show Nat.xor _ (Nat.mul (bit e n) (F n)) = _
    rw [mul_bit]
    rfl

private theorem xorBits_congr_f {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, f j = g j) (v : ℕ) :
    xorBits n f v = xorBits n g v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [xorBits_succ, xorBits_succ, ih (fun j hj => h j (by omega)), h n (by omega)]

private theorem xorBits_zero_v (n : ℕ) (f : ℕ → ℕ) : xorBits n f 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [xorBits_succ, ih]; simp

private theorem evV_eq (P v : ℕ) : evV P v = evalV (unpack6 P) v := by
  unfold evV evalV
  rw [show (Nat.rec (motive := fun _ => ℕ) 0 (fun j acc => Nat.xor acc (Nat.mul (bit v j) (fld6 P j))) 6 : ℕ)
    = xorBits 6 (fld6 P) v from rec_xor_eq (fld6 P) v 6]
  exact xorBits_congr_f (fun j hj => (getD_unpack6 hj).symm) v

private theorem evV_lt (P v : ℕ) : evV P v < 64 := by
  rw [evV_eq]
  unfold evalV
  refine xorBits_lt (n := 6) (fun j hj => ?_) v
  rw [getD_unpack6 hj]; exact fld6_lt _ _

private theorem evalV_zero (l : List ℕ) : evalV l 0 = 0 := xorBits_zero_v _ _

private def lane (w X k : ℕ) : ℕ := (X >>> (w * k)) &&& (2 ^ w - 1)

private def packRec (w : ℕ) (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.lor acc (Nat.shiftLeft (f i) (Nat.mul w i))) n

private theorem lane_testBit (w X k i : ℕ) :
    (lane w X k).testBit i = (decide (i < w) && X.testBit (w * k + i)) := by
  unfold lane
  rw [Nat.testBit_land, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  exact Bool.and_comm _ _

private theorem lane_zero (w k : ℕ) : lane w 0 k = 0 := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [lane_testBit]; simp

private theorem lane_lor_shift (w X y p k : ℕ) (hy : y < 2 ^ w) :
    lane w (X ||| (y <<< (w * p))) k = lane w X k ||| (if k = p then y else 0) := by
  have hy' : ∀ i, w ≤ i → y.testBit i = false := fun i hi =>
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) hi))
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [lane_testBit, Nat.testBit_lor, Nat.testBit_lor, lane_testBit, Nat.testBit_shiftLeft]
  by_cases hi : i < w
  · by_cases hk : k = p
    · subst hk
      simp [hi]
    · have h0 : (if k = p then y else 0) = 0 := if_neg hk
      rw [h0]
      rcases lt_or_gt_of_ne hk with hkp | hkp
      · have h1 : w * (k + 1) ≤ w * p := Nat.mul_le_mul_left w hkp
        rw [Nat.mul_succ] at h1
        have h2 : ¬ (w * k + i ≥ w * p) := by omega
        simp [hi, h2]
      · have h1 : w * (p + 1) ≤ w * k := Nat.mul_le_mul_left w hkp
        rw [Nat.mul_succ] at h1
        have : w ≤ w * k + i - w * p := by omega
        simp [hi, hy' _ this]
  · have h1 : (if k = p then y else 0).testBit i = false := by
      split_ifs
      · exact hy' i (by omega)
      · simp
    rw [h1]; simp [hi]

private theorem lane_packRec (w : ℕ) (f : ℕ → ℕ) (n : ℕ) (hf : ∀ i < n, f i < 2 ^ w) (k : ℕ) :
    lane w (packRec w f n) k = if k < n then f k else 0 := by
  induction n with
  | zero => simp [packRec, lane_zero]
  | succ n ih =>
    have e : packRec w f (n + 1) = packRec w f n ||| (f n <<< (w * n)) := rfl
    rw [e, lane_lor_shift _ _ _ _ _ (hf n (by omega)), ih (fun i hi => hf i (by omega))]
    by_cases hk : k = n
    · subst hk; simp
    · by_cases hk' : k < n
      · simp [hk, hk', show k < n + 1 by omega]
      · simp [hk, hk', show ¬ k < n + 1 by omega]

private theorem fld6_lane (P i : ℕ) : fld6 P i = lane 6 P i := rfl

private theorem fld9_lane (P i : ℕ) : fld9 P i = lane 9 P i := rfl

private theorem tabK_eq (P : ℕ) : tabK P = packRec 6 (evV P) 64 := rfl

private theorem lk_tabK (P : ℕ) {v : ℕ} (hv : v < 64) : lk (tabK P) v = evV P v := by
  unfold lk
  rw [fld6_lane, tabK_eq, lane_packRec 6 _ 64 (fun i _ => evV_lt P i) v, if_pos hv]

private theorem compK_eq (A B : ℕ) : compK A B = packRec 6 (fun i => evV A (fld6 B i)) 6 := rfl

private theorem compK_unpack (A B : ℕ) :
    unpack6 (compK A B) = compT (unpack6 A) (unpack6 B) := by
  have h1 : ∀ i, i < 6 → fld6 (compK A B) i = evalV (unpack6 A) (fld6 B i) := by
    intro i hi
    rw [fld6_lane, compK_eq, lane_packRec 6 _ 6 (fun i _ => evV_lt A _) i, if_pos hi, evV_eq]
  have h2 : unpack6 B = (List.range 6).map fun i => fld6 B i := by
    simp [unpack6, fld6_eq]
  have h3 : unpack6 (compK A B) = (List.range 6).map fun i => fld6 (compK A B) i := by
    simp [unpack6, fld6_eq]
  rw [h3, compT, h2, List.map_map]
  exact List.map_congr_left fun i hi => h1 i (List.mem_range.1 hi)

private theorem codeK_eq (P : ℕ) : codeK P = codeT (unpack6 P) := by
  have h : unpack6 P = [fld6 P 0, fld6 P 1, fld6 P 2, fld6 P 3, fld6 P 4, fld6 P 5] := by
    simp [unpack6, List.range_succ, fld6_eq]
  rw [h]
  rfl

private theorem codeK_lt (P : ℕ) : codeK P < 68719476736 := by
  have h : codeK P = 64 * (64 * (64 * (64 * (64 * (64 * 0 + fld6 P 0) + fld6 P 1) + fld6 P 2)
      + fld6 P 3) + fld6 P 4) + fld6 P 5 := rfl
  have := fld6_lt P 0
  have := fld6_lt P 1
  have := fld6_lt P 2
  have := fld6_lt P 3
  have := fld6_lt P 4
  have := fld6_lt P 5
  omega

theorem sortedK_sound' {L : List ℕ} (h : sortedK L = true) :
    strictSorted (L.map fun x => codeT (unpack6 x)) = true := by
  have key : ∀ L : List ℕ,
      (List.rec (motive := fun _ => ℕ × Bool) (68719476736, true)
        (fun x _ ih => (codeK x, andB (Nat.blt (codeK x) ih.1) ih.2)) L).2 = true →
      strictSorted (L.map fun x => codeT (unpack6 x)) = true := by
    intro L
    induction L with
    | nil => intro _; rfl
    | cons x t ih =>
      intro hL
      have hL' : andB (Nat.blt (codeK x) (List.rec (motive := fun _ => ℕ × Bool) (68719476736, true)
        (fun x _ ih => (codeK x, andB (Nat.blt (codeK x) ih.1) ih.2)) t).1)
        (List.rec (motive := fun _ => ℕ × Bool) (68719476736, true)
        (fun x _ ih => (codeK x, andB (Nat.blt (codeK x) ih.1) ih.2)) t).2 = true := hL
      rw [andB_iff] at hL'
      have iht := ih hL'.2
      cases t with
      | nil => rfl
      | cons y s =>
        have hlt : codeK x < codeK y := by
          have := hL'.1
          rwa [Nat.blt_eq] at this
        simp only [List.map_cons] at iht ⊢
        rw [codeK_eq, codeK_eq] at hlt
        simp only [strictSorted, hlt, decide_true, Bool.true_and]
        exact iht
  exact key L h

private theorem outK_eq (a b : ℕ) : outK a b = outer a b := by
  unfold outK outer
  rw [mul_bit, mul_bit, mul_bit]
  exact (Nat.xor_assoc _ _ _).symm

private theorem wp_eq (v : ℕ) : wp v = wpart v := by
  unfold wp wpart
  simp only [Nat.land_eq, Nat.lor_eq, Nat.or_assoc]
  rfl

private theorem xp_eq (v : ℕ) : xp v = xpart v := by
  unfold xp xpart
  simp only [Nat.land_eq, Nat.lor_eq, Nat.or_assoc]
  rfl

private theorem qK_eq (u : Bool) (v : ℕ) : qK (if u then 1 else 0) v = qOf u v := by
  unfold qK qOf
  rw [wp_eq, xp_eq, outK_eq, outK_eq, outK_eq]
  cases u <;> simp [Nat.xor_assoc] <;> rfl

private theorem outer_lt (a b : ℕ) : outer a b < 512 := by
  have h1 : (b &&& 7) < 8 := by
    have := Nat.and_le_right (n := b) (m := 7); omega
  unfold outer
  have e1 : ∀ s : ℕ, (if a.testBit s then (b &&& 7) <<< (3 * s) else 0) < 512 ∨ s ≥ 3 := by
    intro s
    by_cases hs : s < 3
    · left
      split_ifs
      · rw [Nat.shiftLeft_eq]
        interval_cases s <;> simp <;> omega
      · omega
    · right; omega
  have a0 := e1 0
  have a1 := e1 1
  have a2 := e1 2
  simp only [Nat.mul_zero, Nat.shiftLeft_zero] at a0
  simp only [Nat.mul_one] at a1
  have h512 : (512 : ℕ) = 2 ^ 9 := by norm_num
  rw [h512]
  refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow ?_ ?_) ?_
  · rcases a0 with h | h
    · rw [h512] at h; exact h
    · omega
  · rcases a1 with h | h
    · rw [h512] at h; exact h
    · omega
  · rcases a2 with h | h
    · rw [h512] at h; exact h
    · omega

private theorem qOf_zero (u : Bool) : qOf u 0 = 0 := by
  cases u <;> simp [qOf, wpart, xpart, outer]

private theorem qOf_lt (u : Bool) (v : ℕ) : qOf u v < 512 := by
  have h512 : (512 : ℕ) = 2 ^ 9 := by norm_num
  unfold qOf
  rw [h512]
  refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow ?_ ?_) ?_
  · have := outer_lt (wpart v) (wpart v); omega
  · have := outer_lt (wpart v) (xpart v); omega
  · split_ifs
    · have := outer_lt (xpart v) (xpart v); omega
    · omega

private theorem bEntK_letN (y : ℕ) (k : ℕ → ℕ) : bEntK.letN y k = k y := by cases y <;> rfl

private theorem bEntK_eq (u : Bool) (P : ℕ) {i j : ℕ} (hi : i < 3) (hj : j < 3) :
    bEntK (if u then 1 else 0) P (3 * i + j) = (bOf u (unpack6 P)).getD (3 * i + j) 0 := by
  have hget : (bOf u (unpack6 P)).getD (3 * i + j) 0 = if i = j then
      qOf u (evalV (unpack6 P) (mkv (2 ^ i) 0)) else
      qOf u (evalV (unpack6 P) (mkv (2 ^ i) (2 ^ j))) ^^^ qOf u (evalV (unpack6 P) (mkv (2 ^ i) 0)) ^^^
        (if u then qOf u (evalV (unpack6 P) (mkv 0 (2 ^ j))) else 0) := by
    have h1 : (3 * i + j) / 3 = i := by omega
    have h2 : (3 * i + j) % 3 = j := by omega
    have h3 : 3 * i + j < 9 := by omega
    rw [List.getD_eq_getElem?_getD]
    unfold bOf spanW
    rw [List.getElem?_map, List.getElem?_map, List.getElem?_range h3]
    simp only [Option.map_some, Option.getD_some, h1, h2]
    by_cases hij : i = j
    · simp [hij, qOf_zero, evalV_zero]
    · cases u <;> simp [hij, qOf_zero, evalV_zero]
  rw [hget]
  have e1 : mkv (2 ^ i) 0 = 4 ^ i := by
    clear hget; interval_cases i <;> decide
  have e2 : mkv 0 (2 ^ j) = 2 * 4 ^ j := by
    clear hget; interval_cases j <;> decide
  have e3 : mkv (2 ^ i) (2 ^ j) = 4 ^ i + 2 * 4 ^ j := by
    clear hget; interval_cases i <;> interval_cases j <;> decide
  rw [e1, e2, e3]
  have hd : Nat.div (3 * i + j) 3 = i := by show (3 * i + j) / 3 = i; omega
  have hm : Nat.mod (3 * i + j) 3 = j := by show (3 * i + j) % 3 = j; omega
  unfold bEntK
  rw [bEntK_letN, bEntK_letN, hd, hm]
  by_cases hij : i = j
  · subst hij
    rw [Nat.beq_refl, if_pos rfl]
    show qK (if u then 1 else 0) (evV P (4 ^ i)) = _
    rw [qK_eq, evV_eq]
  · have hb : Nat.beq i j = false := by
      cases h : Nat.beq i j
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hij
    rw [hb, if_neg hij]
    show Nat.xor (qK (if u then 1 else 0) (evV P (4 ^ i + 2 * 4 ^ j)))
      (Nat.xor (qK (if u then 1 else 0) (evV P (4 ^ i)))
        (Nat.mul (if u then 1 else 0) (qK (if u then 1 else 0) (evV P (2 * 4 ^ j))))) = _
    rw [qK_eq, qK_eq, qK_eq, evV_eq, evV_eq, evV_eq]
    cases u <;> simp [Nat.xor_assoc] <;> rfl

private theorem bEntK_lt (u : Bool) (P k : ℕ) : bEntK (if u then 1 else 0) P k < 512 := by
  have h512 : (512 : ℕ) = 2 ^ 9 := by norm_num
  unfold bEntK
  rw [bEntK_letN, bEntK_letN]
  generalize Nat.beq (Nat.div k 3) (Nat.mod k 3) = b
  have hq : ∀ v, qK (if u then 1 else 0) v < 2 ^ 9 := fun v => by
    rw [qK_eq, ← h512]; exact qOf_lt u v
  cases b
  · dsimp only
    refine Nat.xor_lt_two_pow (hq _) (Nat.xor_lt_two_pow (hq _) ?_)
    cases u
    · simp
    · simpa using hq _
  · exact h512 ▸ hq _

private theorem bOfK_eq (u : ℕ) (P : ℕ) : bOfK u P = packRec 9 (bEntK u P) 9 := rfl

private theorem fld9_bOfK (u : Bool) (P : ℕ) {k : ℕ} (hk : k < 9) :
    fld9 (bOfK (if u then 1 else 0) P) k = (bOf u (unpack6 P)).getD k 0 := by
  rw [fld9_lane, bOfK_eq, lane_packRec 9 _ 9 (fun i _ => bEntK_lt u P i) k, if_pos hk]
  have hk' : k = 3 * (k / 3) + k % 3 := by omega
  conv_lhs => rw [hk']
  conv_rhs => rw [hk']
  exact bEntK_eq u P (by omega) (Nat.mod_lt _ (by norm_num))

private theorem evE_eq (u : Bool) (P e : ℕ) :
    evE (bOfK (if u then 1 else 0) P) e = evalE (bOf u (unpack6 P)) e := by
  unfold evE evalE
  rw [rec_xor_eq (fld9 (bOfK (if u then 1 else 0) P)) e 9]
  exact xorBits_congr_f (fun j hj => fld9_bOfK u P hj) e

theorem validK_sound' (u : Bool) {P : ℕ} (h : validK (if u then 1 else 0) P = true) :
    validT u (unpack6 P) = true := by
  unfold validK at h
  rw [letB_eq', letB_eq', andB_iff, andB_iff] at h
  obtain ⟨-, h1, h2⟩ := h
  rw [allN_iff'] at h1 h2
  have hlen : (unpack6 P).length = 6 := by simp [unpack6]
  have hall : ∀ x ∈ unpack6 P, x < 64 := by
    intro x hx
    simp only [unpack6, List.mem_map, List.mem_range] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact Nat.mod_lt _ (by norm_num)
  unfold validT
  have hall' : (∀ x ∈ unpack6 P, x < 64) = True := eq_true hall
  simp only [hlen, hall', List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, bne_iff_ne, ne_eq, true_and]
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · by_cases h0 : v = 0
    · simp [h0]
    · have h3 := h1 (v - 1) (by omega)
      rw [notB_iff, show (v - 1).succ = v by omega, lk_tabK P hv] at h3
      have h4 : evalV (unpack6 P) v ≠ 0 := by
        rw [← evV_eq]
        intro h5
        have : eqN (evV P v) 0 = true := (nbeq_iff _ _).2 h5
        rw [this] at h3
        exact absurd h3 (by decide)
      simp [h4]
  · have h3 := h2 v hv
    rw [lk_tabK P hv, qK_eq, qK_eq, evE_eq, evV_eq] at h3
    exact (nbeq_iff _ _).1 h3

private theorem eqN_iff {a b : ℕ} : eqN a b = true ↔ a = b := nbeq_iff a b

private theorem unpack6_omK : unpack6 omK = omT := by decide +kernel

private theorem unpack6_om2K : unpack6 om2K = compT omT omT := by decide +kernel

private theorem sgn_u (P : ℕ) (h : sgnK 1 P = true) :
    compT (unpack6 P) omT = compT omT (unpack6 P) ∨
      compT (unpack6 P) omT = compT (compT omT omT) (unpack6 P) := by
  have h' : orB (eqN (compK P omK) (compK omK P)) (eqN (compK P omK) (compK om2K P)) = true := h
  rw [orB_iff, eqN_iff, eqN_iff] at h'
  have e1 := compK_unpack P omK
  rw [unpack6_omK] at e1
  rcases h' with h' | h'
  · left
    have e2 := compK_unpack omK P
    rw [unpack6_omK] at e2
    rw [← e1, ← e2, h']
  · right
    have e2 := compK_unpack om2K P
    rw [unpack6_om2K] at e2
    rw [← e1, ← e2, h']

private theorem sgn_l (P : ℕ) (h : sgnK 0 P = true) : sgnOK false (unpack6 P) = true := by
  have h' := h
  unfold sgnK at h'
  rw [show Nat.beq 0 1 = false from rfl] at h'
  dsimp only at h'
  have hNl : imNl (unpack6 P) = [evalV (unpack6 P) 2, evalV (unpack6 P) 8, evalV (unpack6 P) 32] :=
    by simp [imNl, List.range_succ, mkv]
  have hNr : imNr (unpack6 P) = [evalV (unpack6 P) 3, evalV (unpack6 P) 12, evalV (unpack6 P) 48] :=
    by simp [imNr, List.range_succ, mkv]
  simp only [orB_iff, andB_iff, inNl, inNr, eqN_iff, wp_eq, xp_eq, evV_eq] at h'
  unfold sgnOK
  simp only [Bool.false_eq_true, if_false, hNl, hNr]
  simpa using h'

theorem sgnK_sound' (u : Bool) {P : ℕ} (h : sgnK (if u then 1 else 0) P = true) :
    sgnOK u (unpack6 P) = true := by
  cases u
  · exact sgn_l P h
  · have := sgn_u P h
    unfold sgnOK
    simp only [if_true]
    rcases this with h | h <;> simp [h]

end CFSG.KC.Misc.Oq

end
