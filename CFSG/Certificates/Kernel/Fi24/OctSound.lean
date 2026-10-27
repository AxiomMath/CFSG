module

public import Certificates.Data.Kernel.Fi24Oct
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Bound.Init
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.Fi24Oct

open CFSG.KC.Loop Finset

theorem forceB_eq (y : Nat) (k : Nat → Bool) : forceB y k = k y := by
  cases y <;> rfl

theorem nget_eq (L : List Nat) (i : Nat) : nget L i = L.getD i 0 := by
  induction L generalizing i with
  | nil => rfl
  | cons x L ih =>
    cases i with
    | zero => rfl
    | succ n =>
      change nget L n = _
      rw [ih]
      simp

theorem bAnd_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem nIf_eq (c : Bool) (t e : Nat) : Bool.rec (motive := fun _ => Nat) e t c =
    (if c then t else e) := by
  cases c <;> rfl

theorem allN_iff {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    change Bool.rec (motive := fun _ => Bool) false (allN n f) (f n) = true ↔ _
    rw [bAnd_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · exact fun H => ⟨H n (by omega), fun i hi => H i (by omega)⟩

theorem beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem bitN_eq (m i : Nat) : bitN m i = if m.testBit i then 1 else 0 := by
  have h : bitN m i = m / 2 ^ i % 2 := by
    change (m >>> i) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [h, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ i) with e | e <;> simp [e]

theorem bitB_eq (m i : Nat) : bitB m i = m.testBit i := by
  unfold bitB
  rw [bitN_eq]
  cases m.testBit i <;> rfl

theorem testBit_bitN (m i b : Nat) : (bitN m i).testBit b = (decide (b = 0) && m.testBit i) := by
  rw [bitN_eq]
  cases m.testBit i <;> cases b <;> simp [Nat.testBit_succ]

theorem shl_one (n : Nat) : Nat.shiftLeft 1 n = 2 ^ n := Nat.one_shiftLeft n

theorem low24_eq (x : Nat) : low24 x = x % 2 ^ 24 := by
  change x &&& ((1 <<< 24) - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]

theorem low24_lt (x : Nat) : low24 x < 2 ^ 24 := by
  rw [low24_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem testBit_laneK (w Q i b : Nat) :
    (laneK w Q i).testBit b = (decide (b < w) && Q.testBit (w * i + b)) := by
  change ((Q >>> (w * i)) &&& ((1 <<< w) - 1)).testBit b = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight]

theorem packK_cons (w : Nat) (f : Nat → Nat) (x : Nat) (L : List Nat) (j : Nat) :
    packK w f (x :: L) j = f x <<< (w * j) ||| packK w f L (j + 1) := rfl

theorem testBit_packK {w : Nat} (hw : 0 < w) {f : Nat → Nat} (hf : ∀ x, f x < 2 ^ w) :
    ∀ (L : List Nat) (j b : Nat), (packK w f L j).testBit b =
      (decide (w * j ≤ b) && decide (b < w * j + w * L.length) &&
        (f (L.getD ((b - w * j) / w) 0)).testBit ((b - w * j) % w)) := by
  intro L
  induction L with
  | nil =>
    intro j b
    have : packK w f [] j = 0 := rfl
    rw [this, Nat.zero_testBit]
    simp
  | cons x L ih =>
    intro j b
    rw [packK_cons, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
    have e1 : w * (j + 1) = w * j + w := by ring
    have e3 : w * (x :: L).length = w + w * L.length := by simp; ring
    rw [e1, e3]
    rcases Nat.lt_or_ge b (w * j) with h1 | h1
    · have h2 : ¬ w * j + w ≤ b := by omega
      have h3 : ¬ w * j ≤ b := by omega
      simp [h2, h3]
    · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h1
      rw [Nat.add_sub_cancel_left]
      rcases Nat.lt_or_ge t w with h2 | h2
      · have h3 : ¬ w * j + w ≤ w * j + t := by omega
        have h4 : w * j + t < w * j + (w + w * L.length) := by omega
        simp [h3, h4, Nat.div_eq_of_lt h2, Nat.mod_eq_of_lt h2]
      · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le h2
        have hlt : (f x).testBit (w + s) = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hf x) (Nat.pow_le_pow_right (by norm_num)
            (by omega)))
        have e4 : w * j + (w + s) - (w * j + w) = s := by omega
        have e5 : (w + s) / w = s / w + 1 := by rw [Nat.add_comm, Nat.add_div_right _ hw]
        have e6 : (w + s) % w = s % w := by rw [Nat.add_comm, Nat.add_mod_right]
        have e7 : (w * j + (w + s) < w * j + w + w * L.length) ↔
            (w * j + (w + s) < w * j + (w + w * L.length)) := by omega
        simp [hlt, e4, e5, e6, e7]

theorem lane_packK {w : Nat} (hw : 0 < w) {f : Nat → Nat} (hf : ∀ x, f x < 2 ^ w)
    {L : List Nat} {j : Nat} (hj : j < L.length) : laneK w (packK w f L 0) j = f (L.getD j 0) := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_laneK, testBit_packK hw hf]
  by_cases hb : b < w
  · have hq : (w * j + b) / w = j := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt hb, Nat.zero_add]
    have hm : (w * j + b) % w = b := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
    have hlt : w * j + b < w * L.length := by
      have h1 : w * (j + 1) ≤ w * L.length := Nat.mul_le_mul_left w hj
      have e1 : w * (j + 1) = w * j + w := by ring
      omega
    simp [hb, hlt, hq, hm]
  · have hlt : (f (L.getD j 0)).testBit b = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hf _) (Nat.pow_le_pow_right (by omega)
        (by omega)))
    simp only [hb, decide_false, Bool.false_and, hlt]

theorem pcK_eq (m n : Nat) : pcK m n = ∑ i ∈ range n, if m.testBit i then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change bitN m n + pcK m n = _
    rw [ih, sum_range_succ, bitN_eq, Nat.add_comm]

theorem cardStep_eq (m : Nat) (b : Bool) : cardStep m b = (cardOne m && b) := by
  unfold cardStep
  generalize cardOne m = c
  cases c <;> rfl

theorem cardK_cons (m : Nat) (L : List Nat) : cardK (m :: L) = (cardOne m && cardK L) := by
  have e : cardK (m :: L) = cardStep m (cardK L) := rfl
  rw [e, cardStep_eq]

theorem cardK_sound {L : List Nat} (h : cardK L = true) :
    ∀ m ∈ L, (∑ i ∈ range 24, if m.testBit i then 1 else 0) = 8 := by
  induction L with
  | nil => simp
  | cons m L ih =>
    rw [cardK_cons, Bool.and_eq_true, cardOne, Nat.beq_eq, pcK_eq] at h
    intro m' hm'
    rcases List.mem_cons.1 hm' with rfl | hm'
    · exact h.1
    · exact ih h.2 m' hm'

@[expose] def ThrRep (a b c d e : Nat) (f : Nat → Nat) : Prop :=
  ∀ j, a.testBit j = decide (1 ≤ f j) ∧ b.testBit j = decide (2 ≤ f j) ∧
    c.testBit j = decide (3 ≤ f j) ∧ d.testBit j = decide (4 ≤ f j) ∧
    e.testBit j = decide (5 ≤ f j)

theorem thrRep_zero : ThrRep 0 0 0 0 0 fun _ => 0 := by
  intro j
  simp

theorem thrRep_step {a b c d e : Nat} {f : Nat → Nat} (h : ThrRep a b c d e f) (x : Nat) :
    ThrRep (a ||| x) (b ||| (a &&& x)) (c ||| (b &&& x)) (d ||| (c &&& x)) (e ||| (d &&& x))
      fun j => f j + if x.testBit j then 1 else 0 := by
  intro j
  obtain ⟨h1, h2, h3, h4, h5⟩ := h j
  simp only [Nat.testBit_or, Nat.testBit_and, h1, h2, h3, h4, h5]
  by_cases hx : x.testBit j = true
  · simp only [hx, ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> apply Bool.eq_iff_iff.2 <;> simp <;> omega
  · simp [hx]

theorem thrK_succ (Q m : Nat) (k : Nat → Nat → Nat → Nat → Nat → Bool) (n a b c d e : Nat) :
    thrK Q m k (n + 1) a b c d e =
      if m.testBit n = true then
        thrK Q m k n (a ||| laneK 1024 Q n) (b ||| (a &&& laneK 1024 Q n))
          (c ||| (b &&& laneK 1024 Q n)) (d ||| (c &&& laneK 1024 Q n))
          (e ||| (d &&& laneK 1024 Q n))
      else thrK Q m k n a b c d e := by
  have e : thrK Q m k (n + 1) a b c d e = Bool.rec (motive := fun _ => Bool)
      (thrK Q m k n a b c d e)
      (forceB (laneK 1024 Q n) fun x =>
        forceB (Nat.lor a x) fun a' => forceB (Nat.lor b (Nat.land a x)) fun b' =>
        forceB (Nat.lor c (Nat.land b x)) fun c' => forceB (Nat.lor d (Nat.land c x)) fun d' =>
        forceB (Nat.lor e (Nat.land d x)) fun e' => thrK Q m k n a' b' c' d' e')
      (bitB m n) := rfl
  rw [e, bitB_eq]
  cases m.testBit n
  · rfl
  · simp only [forceB_eq, ↓reduceIte]
    rfl

theorem thrK_spec (Q m : Nat) (k : Nat → Nat → Nat → Nat → Nat → Bool) :
    ∀ (n a b c d e : Nat) (f : Nat → Nat), ThrRep a b c d e f →
      ∃ a' b' c' d' e', thrK Q m k n a b c d e = k a' b' c' d' e' ∧
        ThrRep a' b' c' d' e' fun j =>
          f j + ∑ i ∈ range n, if m.testBit i ∧ (laneK 1024 Q i).testBit j then 1 else 0 := by
  intro n
  induction n with
  | zero =>
    intro a b c d e f h
    exact ⟨a, b, c, d, e, rfl, by simpa using h⟩
  | succ n ih =>
    intro a b c d e f h
    rw [thrK_succ]
    by_cases hm : m.testBit n = true
    · simp only [hm, ↓reduceIte]
      obtain ⟨a', b', c', d', e', h1, h2⟩ := ih _ _ _ _ _ _ (thrRep_step h (laneK 1024 Q n))
      refine ⟨a', b', c', d', e', h1, ?_⟩
      convert h2 using 2 with j
      rw [sum_range_succ]
      simp only [hm, true_and]
      ring
    · simp only [hm, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨a', b', c', d', e', h1, h2⟩ := ih _ _ _ _ _ _ h
      refine ⟨a', b', c', d', e', h1, ?_⟩
      convert h2 using 2 with j
      rw [sum_range_succ]
      simp [hm]

theorem pairOneK_sound {Q k m : Nat} (h : pairOneK Q k m = true) {j : Nat} (hj : j ≠ k) :
    (∑ i ∈ range 24, if m.testBit i ∧ (laneK 1024 Q i).testBit j then 1 else 0) ≤ 4 := by
  obtain ⟨a', b', c', d', e', h1, h2⟩ := thrK_spec Q m (onlyK k) 24 0 0 0 0 0 _ thrRep_zero
  have h' : onlyK k a' b' c' d' e' = true := by
    unfold pairOneK at h
    rw [h1] at h
    exact h
  have he : e' ||| 1 <<< k = 1 <<< k := Nat.eq_of_beq_eq_true h'
  have hb := congrArg (fun z => z.testBit j) he
  simp only [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Ne.symm hj, decide_false,
    Bool.or_false] at hb
  have h5 := (h2 j).2.2.2.2
  simp only [hb, zero_add] at h5
  by_contra hc
  have : 5 ≤ ∑ i ∈ range 24, if m.testBit i ∧ (laneK 1024 Q i).testBit j then 1 else 0 := by
    omega
  simp [this] at h5

theorem testBit_plane (L : List Nat) (i j : Nat) :
    (packK 1 (fun x => bitN x i) L 0).testBit j =
      (decide (j < L.length) && (L.getD j 0).testBit i) := by
  have hf : ∀ x, bitN x i < 2 ^ 1 := fun x => by rw [bitN_eq]; split <;> norm_num
  rw [testBit_packK (by norm_num) hf, testBit_bitN]
  simp [Nat.mod_one]

theorem testBit_planesN (L : List Nat) (hL : L.length ≤ 1024) {i0 j : Nat} (hj : j < 1024) :
    ∀ n, (Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => Nat.lor (Nat.shiftLeft (packK 1 (fun x => bitN x i) L 0)
        (Nat.mul 1024 i)) acc) n : Nat).testBit (1024 * i0 + j) =
      (decide (i0 < n) && (packK 1 (fun x => bitN x i0) L 0).testBit j) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    change ((packK 1 (fun x => bitN x n) L 0 <<< (1024 * n)) ||| _).testBit _ = _
    rw [Nat.testBit_or, ih, Nat.testBit_shiftLeft]
    rcases Nat.lt_trichotomy i0 n with h | rfl | h
    · have : ¬ 1024 * n ≤ 1024 * i0 + j := by omega
      simp [this, h, Nat.lt_succ_of_lt h]
    · simp
    · have h1 : 1024 * n ≤ 1024 * i0 + j := by omega
      have h2 : ¬ 1024 * i0 + j - 1024 * n < L.length := by omega
      have h3 : ¬ i0 < n + 1 := by omega
      have h4 : ¬ i0 < n := by omega
      simp [h1, testBit_plane, h2, h3, h4]

theorem testBit_lane_planes {L : List Nat} (hL : L.length ≤ 1024) {i : Nat} (hi : i < 24)
    (j : Nat) : (laneK 1024 (planesK L) i).testBit j =
      (decide (j < L.length) && (L.getD j 0).testBit i) := by
  rw [testBit_laneK]
  by_cases hj : j < 1024
  · have e := testBit_planesN L hL (i0 := i) hj 24
    change (planesK L).testBit (1024 * i + j) = _ at e
    rw [e, testBit_plane]
    simp [hj, hi]
  · have : ¬ j < L.length := by omega
    simp [hj, this]

theorem pairK_sound {L : List Nat} (h : pairK L = true) (hL : L.length = 759) {k k' : Nat}
    (hk : k < 759) (hk' : k' < 759) (hne : k ≠ k') :
    (∑ i ∈ range 24, if (L.getD k 0).testBit i ∧ (L.getD k' 0).testBit i then 1 else 0) ≤ 4 := by
  unfold pairK at h
  rw [forceB_eq, forceB_eq, allN_iff] at h
  have h1 := pairOneK_sound (h k hk) (j := k') (Ne.symm hne)
  rw [lane_packK (by norm_num) low24_lt (by omega)] at h1
  refine Nat.le_trans (le_of_eq (sum_congr rfl fun i hi => ?_)) h1
  have hi' : i < 24 := mem_range.1 hi
  rw [testBit_lane_planes (by omega) hi', low24_eq, Nat.testBit_mod_two_pow]
  simp [hi', hL, hk']

theorem testBit_imgK (P0 P1 : List Nat) (l m x : Nat) : ∀ n, (imgK P0 P1 l m n).testBit x = true ↔
    ∃ i < n, m.testBit i = true ∧
      (if l = 0 then P0.getD i 0 else P1.getD i 0) % 24 = x := by
  intro n
  induction n with
  | zero => simp [imgK]
  | succ n ih =>
    change ((Bool.rec (motive := fun _ => Nat) 0 _ (bitB m n)) ||| imgK P0 P1 l m n).testBit x = true
      ↔ _
    have eπ : (Bool.rec (motive := fun _ => Nat) (nget P1 n) (nget P0 n) (Nat.beq l 0)) =
        if l = 0 then P0.getD n 0 else P1.getD n 0 := by
      rw [nIf_eq, nget_eq, nget_eq]
      by_cases hl : l = 0
      · simp [hl]
      · rw [beq_false_of_ne hl]
        simp [hl]
    rw [Nat.testBit_or, Bool.or_eq_true, ih, bitB_eq, nIf_eq, eπ, shl_one]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · by_cases hm : m.testBit n = true
        · simp only [hm, ↓reduceIte, Nat.testBit_two_pow] at h
          exact ⟨n, by omega, hm, of_decide_eq_true h⟩
        · simp [hm] at h
      · exact ⟨i, by omega, h⟩
    · rintro ⟨i, hi, hm, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inr ⟨i, hi, hm, h⟩
      · left
        simp only [hm, ↓reduceIte, Nat.testBit_two_pow]
        exact decide_eq_true h

theorem treeK_sound {L P B P0 P1 : List Nat} (h : treeK L P B P0 P1 = true) (hL : L.length = 759)
    (hP : P.length = 759) (hB : B.length = 759) {k : Nat} (hk0 : k ≠ 0) (hk : k < 759) :
    P.getD k 0 % 759 < k ∧ ∀ x < 24, ((L.getD k 0).testBit x = true ↔
      ∃ i < 24, (L.getD (P.getD k 0 % 759) 0).testBit i = true ∧
        (if B.getD k 0 % 2 = 0 then P0.getD i 0 else P1.getD i 0) % 24 = x) := by
  unfold treeK at h
  rw [forceB_eq, forceB_eq, forceB_eq, allN_iff] at h
  have h1 := h k hk
  rw [beq_false_of_ne hk0] at h1
  change Bool.rec (motive := fun _ => Bool) false _ _ = true at h1
  rw [bAnd_eq, Bool.and_eq_true] at h1
  have f16 : ∀ x, x % 759 < 2 ^ 16 := fun x =>
    Nat.lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num)
  have f1 : ∀ x, x % 2 < 2 ^ 1 := fun x => Nat.mod_lt _ (by norm_num)
  have eP : laneK 16 (packK 16 (fun x => Nat.mod x 759) P 0) k = P.getD k 0 % 759 :=
    lane_packK (by norm_num) f16 (by omega)
  have eB : laneK 1 (packK 1 (fun x => Nat.mod x 2) B 0) k = B.getD k 0 % 2 :=
    lane_packK (by norm_num) f1 (by omega)
  rw [eP, eB] at h1
  obtain ⟨hp, hm⟩ := h1
  refine ⟨Nat.le_of_ble_eq_true hp, fun x hx => ?_⟩
  rw [lane_packK (by norm_num) low24_lt (by omega),
    lane_packK (by norm_num) low24_lt (by omega)] at hm
  have hm := Nat.eq_of_beq_eq_true hm
  have e : (low24 (L.getD k 0)).testBit x = _ := congrArg (fun z => z.testBit x) hm
  rw [low24_eq, Nat.testBit_mod_two_pow] at e
  simp only [hx, decide_true, Bool.true_and] at e
  rw [e, testBit_imgK]
  refine exists_congr fun i => and_congr_right fun hi => ?_
  rw [low24_eq, Nat.testBit_mod_two_pow]
  simp [hi]

end CFSG.KC.Fi24Oct

end
