module

public import Certificates.Data.Kernel.Bounds.Table
public import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Group
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Certificates.KB.Sound

open CFSG.Certificates.KB

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by
  cases a <;> rfl

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by
  cases a <;> rfl

theorem andB_true_iff {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andB]

theorem orB_true_iff {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp [orB]

theorem ble_false {a b : ℕ} (h : Nat.ble a b = false) : b < a := by
  by_contra h'
  rw [Nat.ble_eq_true_of_le (by omega)] at h
  exact Bool.noConfusion h

theorem beq_false_of_ne {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

@[expose] def pkb (B : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: l => d + B * pkb B l

theorem pkb_nil (B : ℕ) : pkb B [] = 0 := rfl

theorem pkb_cons (B d : ℕ) (l : List ℕ) : pkb B (d :: l) = d + B * pkb B l := rfl

theorem pkb_lt {B : ℕ} : ∀ {l : List ℕ}, (∀ d ∈ l, d < B) → pkb B l < B ^ l.length
  | [], _ => by simp [pkb]
  | d :: l, h => by
    have h1 := h d (by simp)
    have h2 := pkb_lt (l := l) (fun x hx => h x (by simp [hx]))
    rw [pkb_cons, List.length_cons, pow_succ]
    nlinarith [Nat.mul_le_mul_left B h2]

theorem pkb_append (B : ℕ) : ∀ (l₁ l₂ : List ℕ),
    pkb B (l₁ ++ l₂) = pkb B l₁ + B ^ l₁.length * pkb B l₂
  | [], l₂ => by simp [pkb]
  | d :: l, l₂ => by
    rw [List.cons_append, pkb_cons, pkb_cons, pkb_append B l l₂, List.length_cons, pow_succ]
    ring

theorem pkb_div_pow {B : ℕ} (hB : 0 < B) : ∀ (l : List ℕ) (k : ℕ), (∀ d ∈ l, d < B) →
    pkb B l / B ^ k = pkb B (l.drop k)
  | l, 0, _ => by simp
  | [], k + 1, _ => by simp [pkb]
  | d :: l, k + 1, h => by
    have h1 : (d + B * pkb B l) / B = pkb B l := by
      rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt (h d (by simp)), zero_add]
    rw [pkb_cons, pow_succ', ← Nat.div_div_eq_div_mul, h1, List.drop_succ_cons]
    exact pkb_div_pow hB l k (fun x hx => h x (by simp [hx]))

theorem pkb_digit {B : ℕ} (hB : 0 < B) (l : List ℕ) (h : ∀ d ∈ l, d < B) (k : ℕ)
    (hk : k < l.length) : pkb B l / B ^ k % B = l[k] := by
  rw [pkb_div_pow hB l k h, List.drop_eq_getElem_cons hk, pkb_cons, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (h _ (List.getElem_mem hk))]

theorem pkb_mod_pow {B : ℕ} (hB : 0 < B) (l : List ℕ) (h : ∀ d ∈ l, d < B) (k : ℕ) :
    pkb B l % B ^ k = pkb B (l.take k) := by
  have hsplit := pkb_append B (l.take k) (l.drop k)
  rw [List.take_append_drop] at hsplit
  have hlt : pkb B (l.take k) < B ^ k :=
    lt_of_lt_of_le (pkb_lt (fun d hd => h d (List.mem_of_mem_take hd)))
      (Nat.pow_le_pow_right hB (List.length_take_le k l))
  rcases le_or_gt k l.length with hk | hk
  · rw [hsplit, List.length_take_of_le hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · rw [List.drop_eq_nil_of_le hk.le, pkb_nil, mul_zero, add_zero] at hsplit
    rw [hsplit, Nat.mod_eq_of_lt hlt]

theorem pkb_eq_zero {B : ℕ} : ∀ {l : List ℕ}, (∀ d ∈ l, 0 < d) → pkb B l = 0 → l = []
  | [], _, _ => rfl
  | d :: l, h, h0 => by
    have := h d (by simp)
    rw [pkb_cons] at h0
    omega

theorem byte_eq (w i : ℕ) : byte w i = w / 2 ^ (8 * i) % 256 := by
  unfold byte
  change (w >>> (i <<< 3)) &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  norm_num [mul_comm]

theorem byte_eq' (w i : ℕ) : byte w i = w / 256 ^ i % 256 := by
  rw [byte_eq, pow_mul]
  norm_num

theorem byte_lt (w i : ℕ) : byte w i < 256 := by
  rw [byte_eq']
  exact Nat.mod_lt _ (by norm_num)

theorem two_pow_eight_mul (m : ℕ) : 2 ^ (8 * m) = 256 ^ m := by
  rw [pow_mul]
  norm_num

theorem lor_shift (v b m : ℕ) (hv : v < 256 ^ m) :
    Nat.lor v (Nat.shiftLeft b (Nat.shiftLeft m (nat_lit 3))) = v + 256 ^ m * b := by
  change v ||| b <<< (m <<< 3) = _
  have h8 : m <<< 3 = 8 * m := by
    rw [Nat.shiftLeft_eq]
    ring
  rw [← two_pow_eight_mul] at hv ⊢
  rw [h8, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hv, Nat.shiftLeft_eq]
  ring

@[expose] noncomputable def bytes (w n : ℕ) : List ℕ := (List.range n).map (byte w)

theorem bytes_length (w n : ℕ) : (bytes w n).length = n := by
  simp [bytes]

theorem bytes_succ (w n : ℕ) : bytes w (n + 1) = bytes w n ++ [byte w n] := by
  simp [bytes, List.range_succ]

theorem getElem_bytes (w n q : ℕ) (hq : q < (bytes w n).length) : (bytes w n)[q] = byte w q := by
  simp [bytes]

theorem mem_bytes {w n d : ℕ} : d ∈ bytes w n ↔ ∃ q < n, byte w q = d := by
  simp [bytes]

theorem bytes_lt (w n : ℕ) : ∀ d ∈ bytes w n, d < 256 := by
  intro d hd
  obtain ⟨q, -, rfl⟩ := mem_bytes.1 hd
  exact byte_lt w q

theorem bytes_pkb (l : List ℕ) (h : ∀ d ∈ l, d < 256) : bytes (pkb 256 l) l.length = l := by
  apply List.ext_getElem (bytes_length _ _)
  intro q h1 h2
  rw [getElem_bytes, byte_eq', pkb_digit (by norm_num) l h q h2]

theorem byte_pkb (l : List ℕ) (h : ∀ d ∈ l, d < 256) (q : ℕ) (hq : q < l.length) :
    byte (pkb 256 l) q = l[q] := by
  rw [byte_eq', pkb_digit (by norm_num) l h q hq]

theorem bytes_congr {w w' n : ℕ} (h : ∀ q < n, byte w q = byte w' q) : bytes w n = bytes w' n := by
  unfold bytes
  apply List.map_congr_left
  intro q hq
  exact h q (List.mem_range.1 hq)

@[expose] def lv {G : Type*} [Group G] (val : ℕ → G) (l : List ℕ) : G := (l.map val).prod

theorem lv_nil {G : Type*} [Group G] (val : ℕ → G) : lv val [] = 1 := rfl

theorem lv_append {G : Type*} [Group G] (val : ℕ → G) (l₁ l₂ : List ℕ) :
    lv val (l₁ ++ l₂) = lv val l₁ * lv val l₂ := by
  simp [lv]

theorem lv_cons {G : Type*} [Group G] (val : ℕ → G) (d : ℕ) (l : List ℕ) :
    lv val (d :: l) = val d * lv val l := by
  simp [lv]

theorem lv_singleton {G : Type*} [Group G] (val : ℕ → G) (d : ℕ) : lv val [d] = val d := by
  simp [lv]

theorem lv_filter {G : Type*} [Group G] (val : ℕ → G) (eps : ℕ) (h1 : val eps = 1) :
    ∀ l : List ℕ, lv val (l.filter (· ≠ eps)) = lv val l
  | [] => rfl
  | d :: l => by
    by_cases hd : d = eps
    · subst hd
      rw [List.filter_cons_of_neg (by simp), lv_filter val _ h1 l, lv_cons, h1, one_mul]
    · rw [List.filter_cons_of_pos (by simpa using hd), lv_cons, lv_cons, lv_filter val eps h1 l]

theorem strip_succ (eps w n : ℕ) : strip eps w (n + 1) =
    Prod.rec (motive := fun _ => ℕ × ℕ) (fun v m =>
      Bool.rec
        (Prod.mk (Nat.lor v (Nat.shiftLeft (byte w n) (Nat.shiftLeft m (nat_lit 3)))) (Nat.succ m))
        (Prod.mk v m) (Nat.beq (byte w n) eps)) (strip eps w n) := rfl

theorem strip_spec (eps w n : ℕ) : strip eps w n =
    (pkb 256 ((bytes w n).filter (· ≠ eps)), ((bytes w n).filter (· ≠ eps)).length) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [strip_succ, ih, bytes_succ, List.filter_append]
    cases h : Nat.beq (byte w n) eps
    · have hne : byte w n ≠ eps := Nat.ne_of_beq_eq_false h
      have hf : [byte w n].filter (· ≠ eps) = [byte w n] := by simp [hne]
      rw [hf]
      have hlt := pkb_lt (B := 256) (l := (bytes w n).filter (· ≠ eps))
        (fun d hd => bytes_lt w n d (List.mem_of_mem_filter hd))
      change (Nat.lor _ _, _) = _
      rw [lor_shift _ _ _ hlt, pkb_append, pkb_cons, pkb_nil, List.length_append]
      simp
    · have heq : byte w n = eps := Nat.eq_of_beq_eq_true h
      have hf : [byte w n].filter (· ≠ eps) = [] := by simp [heq]
      rw [hf, List.append_nil]

theorem freeRed_succ (inv w n : ℕ) : freeRed inv w (n + 1) =
    Bool.rec (Nat.add (Nat.shiftLeft (freeRed inv w n) (nat_lit 8)) (Nat.succ (byte w n)))
      (Nat.shiftRight (freeRed inv w n) (nat_lit 8))
      (andB (Nat.ble (nat_lit 1) (freeRed inv w n))
        (Nat.beq (Nat.land (freeRed inv w n) (nat_lit 255)) (Nat.succ (byte inv (byte w n))))) :=
  rfl

theorem freeRed_stack {G : Type*} [Group G] (val : ℕ → G) (inv w N : ℕ)
    (hw : ∀ q < N, byte w q < 255)
    (hinv : ∀ q < N, val (byte inv (byte w q)) = (val (byte w q))⁻¹) :
    ∀ n ≤ N, ∃ st : List ℕ, freeRed inv w n = pkb 256 (st.map (· + 1)) ∧ (∀ d ∈ st, d < 255) ∧
      lv val (bytes w n) = lv val st.reverse := by
  intro n hn
  induction n with
  | zero => exact ⟨[], rfl, by simp, rfl⟩
  | succ n ih =>
    obtain ⟨st, hst, hlt, hv⟩ := ih (by omega)
    have hnN : n < N := by omega
    have hpush : ∃ st' : List ℕ, Nat.add (Nat.shiftLeft (freeRed inv w n) (nat_lit 8))
        (Nat.succ (byte w n)) = pkb 256 (st'.map (· + 1)) ∧ (∀ d ∈ st', d < 255) ∧
        lv val (bytes w (n + 1)) = lv val st'.reverse := by
      refine ⟨byte w n :: st, ?_, ?_, ?_⟩
      · change freeRed inv w n <<< 8 + (byte w n + 1) = _
        rw [Nat.shiftLeft_eq, hst, List.map_cons, pkb_cons]
        ring
      · intro d hd
        rcases List.mem_cons.1 hd with rfl | hd
        · exact hw n hnN
        · exact hlt d hd
      · rw [bytes_succ, lv_append, hv, List.reverse_cons, lv_append, lv_singleton]
    rw [freeRed_succ]
    cases hc : andB (Nat.ble (nat_lit 1) (freeRed inv w n))
        (Nat.beq (Nat.land (freeRed inv w n) (nat_lit 255)) (Nat.succ (byte inv (byte w n))))
    · exact hpush
    · obtain ⟨h1, h2⟩ := andB_true_iff.1 hc
      have h1' : 1 ≤ freeRed inv w n := Nat.le_of_ble_eq_true h1
      have h2' : freeRed inv w n % 256 = byte inv (byte w n) + 1 := by
        have := Nat.eq_of_beq_eq_true h2
        change freeRed inv w n &&& (2 ^ 8 - 1) = byte inv (byte w n) + 1 at this
        rwa [Nat.and_two_pow_sub_one_eq_mod] at this
      cases st with
      | nil =>
        rw [hst] at h1'
        simp [pkb] at h1'
      | cons h t =>
        have hh : h < 255 := hlt h (by simp)
        rw [hst, List.map_cons, pkb_cons, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (by omega)] at h2'
        refine ⟨t, ?_, fun d hd => hlt d (by simp [hd]), ?_⟩
        · change freeRed inv w n >>> 8 = _
          rw [Nat.shiftRight_eq_div_pow, hst, List.map_cons, pkb_cons]
          omega
        · have hh' : h = byte inv (byte w n) := by omega
          rw [bytes_succ, lv_append, hv, List.reverse_cons, lv_append, lv_singleton,
            lv_singleton, hh', hinv n hnN, mul_assoc, inv_mul_cancel, mul_one]

theorem freeRed_one {G : Type*} [Group G] (val : ℕ → G) (inv w n : ℕ)
    (hw : ∀ q < n, byte w q < 255)
    (hinv : ∀ q < n, val (byte inv (byte w q)) = (val (byte w q))⁻¹)
    (h : freeRed inv w n = 0) : lv val (bytes w n) = 1 := by
  obtain ⟨st, hst, -, hv⟩ := freeRed_stack val inv w n hw hinv n le_rfl
  rw [h] at hst
  have := pkb_eq_zero (B := 256) (l := st.map (· + 1)) (by simp) hst.symm
  rw [List.map_eq_nil_iff] at this
  rw [hv, this]
  rfl

theorem shiftLeft_three (m : ℕ) : m <<< 3 = 8 * m := by
  rw [Nat.shiftLeft_eq]
  ring

theorem rot_pkb (l : List ℕ) (h : ∀ d ∈ l, d < 256) (s : ℕ) :
    rot (pkb 256 l) l.length s = pkb 256 (l.drop s ++ l.take s) := by
  unfold rot
  change (pkb 256 l >>> (s <<< 3)) |||
    ((pkb 256 l &&& ((1 <<< (s <<< 3)) - 1)) <<< ((l.length - s) <<< 3)) = _
  rw [shiftLeft_three, shiftLeft_three, Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow, two_pow_eight_mul s, pkb_div_pow (by norm_num) l s h,
    pkb_mod_pow (by norm_num) l h s]
  have hd : pkb 256 (l.drop s) < 2 ^ (8 * (l.length - s)) := by
    rw [two_pow_eight_mul]
    have := pkb_lt (B := 256) (l := l.drop s) (fun d hd => h d (List.mem_of_mem_drop hd))
    rwa [List.length_drop] at this
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hd, Nat.shiftLeft_eq, two_pow_eight_mul,
    pkb_append, List.length_drop]
  ring

theorem isRot_spec {r n w : ℕ} (h : isRot r n w = true) : ∃ s < n, rot r n s = w := by
  have key : ∀ k, Nat.rec (motive := fun _ => Bool) false
      (fun s acc => orB (Nat.beq (rot r n s) w) acc) k = true → ∃ s < k, rot r n s = w := by
    intro k
    induction k with
    | zero => exact fun h => absurd h Bool.false_ne_true
    | succ k ih =>
      intro h
      rcases orB_true_iff.1 h with h | h
      · exact ⟨k, by omega, Nat.eq_of_beq_eq_true h⟩
      · obtain ⟨s, hs, e⟩ := ih h
        exact ⟨s, by omega, e⟩
  exact key n h

theorem lv_rotate {G : Type*} [Group G] (val : ℕ → G) (l : List ℕ) (s : ℕ) (h : lv val l = 1) :
    lv val (l.drop s ++ l.take s) = 1 := by
  rw [← List.take_append_drop s l, lv_append] at h
  rw [lv_append, eq_inv_of_mul_eq_one_right h, inv_mul_cancel]

theorem land_mask (x k : ℕ) : x &&& (2 ^ k - 1) = x % 2 ^ k := Nat.and_two_pow_sub_one_eq_mod x k

theorem wN_eq (w : ℕ) : wN w = w % 256 := by
  unfold wN
  change w &&& (2 ^ 8 - 1) = _
  rw [land_mask]
  norm_num

theorem wKind_eq (w : ℕ) : wKind w = w / 256 % 2 := by
  unfold wKind
  change (w >>> 8) &&& (2 ^ 1 - 1) = _
  rw [land_mask, Nat.shiftRight_eq_div_pow]
  norm_num

theorem wBase_eq (w : ℕ) : wBase w = w / 512 % 32768 := by
  unfold wBase
  change (w >>> 9) &&& (2 ^ 15 - 1) = _
  rw [land_mask, Nat.shiftRight_eq_div_pow]
  norm_num

theorem wLetters_eq (w : ℕ) : wLetters w = w / 2 ^ 24 := by
  unfold wLetters
  change w >>> 24 = _
  rw [Nat.shiftRight_eq_div_pow]

theorem letter_eq (w q : ℕ) : letter w q = byte (wLetters w) q := by
  unfold letter
  change (w >>> (24 + (q <<< 3))) &&& (2 ^ 8 - 1) = _
  rw [land_mask, Nat.shiftRight_eq_div_pow, shiftLeft_three, byte_eq, wLetters_eq, pow_add,
    Nat.div_div_eq_div_mul]
  norm_num

@[expose] noncomputable def wbytes (w : ℕ) : List ℕ := bytes (wLetters w) (wN w)

@[expose] noncomputable def pr (inv w q : ℕ) : ℕ := letter w q + 256 * byte inv (letter w q)

theorem pr_lt (inv w q : ℕ) : pr inv w q < 65536 := by
  unfold pr
  have h1 := byte_lt (wLetters w) q
  have h2 := byte_lt inv (letter w q)
  rw [← letter_eq] at h1
  omega

theorem pairs_aux (inv w : ℕ) : ∀ k, Nat.rec (motive := fun _ => ℕ) (Nat.land w (nat_lit 16777215))
    (fun q acc => Nat.lor acc (Nat.shiftLeft
      (Nat.lor (letter w q) (Nat.shiftLeft (byte inv (letter w q)) (nat_lit 8)))
      (Nat.add (nat_lit 24) (Nat.shiftLeft q (nat_lit 4))))) k =
    w % 2 ^ 24 + 2 ^ 24 * pkb 65536 ((List.range k).map (pr inv w)) := by
  intro k
  induction k with
  | zero =>
    change w &&& (2 ^ 24 - 1) = _
    rw [land_mask]
    simp [pkb]
  | succ k ih =>
    change (Nat.rec (motive := fun _ => ℕ) (Nat.land w (nat_lit 16777215))
      (fun q acc => Nat.lor acc (Nat.shiftLeft
        (Nat.lor (letter w q) (Nat.shiftLeft (byte inv (letter w q)) (nat_lit 8)))
        (Nat.add (nat_lit 24) (Nat.shiftLeft q (nat_lit 4))))) k) |||
      ((letter w k ||| (byte inv (letter w k) <<< 8)) <<< (24 + (k <<< 4))) = _
    rw [ih]
    have hl : letter w k < 2 ^ 8 := by
      have := byte_lt (wLetters w) k
      rw [← letter_eq] at this
      simpa using this
    have hp : letter w k ||| (byte inv (letter w k) <<< 8) = pr inv w k := by
      rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hl, Nat.shiftLeft_eq, pr]
      ring
    have hk4 : k <<< 4 = 16 * k := by
      rw [Nat.shiftLeft_eq]
      ring
    have hY := pkb_lt (B := 65536) (l := (List.range k).map (pr inv w))
      (fun d hd => by
        obtain ⟨q, -, rfl⟩ := List.mem_map.1 hd
        exact pr_lt inv w q)
    rw [List.length_map, List.length_range] at hY
    have h16 : (65536 : ℕ) ^ k = 2 ^ (16 * k) := by
      rw [pow_mul]
      norm_num
    have hacc : w % 2 ^ 24 + 2 ^ 24 * pkb 65536 ((List.range k).map (pr inv w)) <
        2 ^ (24 + 16 * k) := by
      have hm := Nat.mod_lt w (show 0 < 2 ^ 24 by positivity)
      rw [pow_add, ← h16]
      nlinarith [Nat.mul_le_mul_left (2 ^ 24) hY]
    rw [hp, hk4, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hacc, Nat.shiftLeft_eq,
      List.range_succ, List.map_append, pkb_append, List.map_singleton, pkb_cons, pkb_nil,
      List.length_map, List.length_range, pow_add, h16]
    ring

theorem pairs_eq (inv w : ℕ) :
    pairs inv w = w % 2 ^ 24 + 2 ^ 24 * pkb 65536 ((List.range (wN w)).map (pr inv w)) :=
  pairs_aux inv w (wN w)

theorem pairs_low (inv w : ℕ) : pairs inv w % 256 = w % 256 := by
  rw [pairs_eq]
  have h : (2 : ℕ) ^ 24 = 256 * 2 ^ 16 := by norm_num
  rw [h, mul_assoc, Nat.add_mul_mod_self_left, Nat.mod_mod_of_dvd _ (by norm_num)]

theorem pairs_kind (inv w : ℕ) : pairs inv w / 256 % 2 = w / 256 % 2 := by
  rw [pairs_eq]
  have h : (2 : ℕ) ^ 24 = 256 * 2 ^ 16 := by norm_num
  rw [h, mul_assoc, Nat.add_mul_div_left _ _ (by norm_num), Nat.mod_mul_right_div_self]
  have h2 : (2 : ℕ) ^ 16 = 2 * 2 ^ 15 := by norm_num
  rw [h2, mul_assoc, Nat.add_mul_mod_self_left, Nat.mod_mod_of_dvd _ (by norm_num)]

theorem pairs_pair (inv w q : ℕ) (hq : q < wN w) :
    pairs inv w / 2 ^ (24 + 16 * q) % 65536 = pr inv w q := by
  rw [pairs_eq, pow_add, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt (Nat.mod_lt _ (by positivity)), zero_add]
  have h16 : (2 : ℕ) ^ (16 * q) = 65536 ^ q := by
    rw [pow_mul]
    norm_num
  rw [h16, pkb_digit (by norm_num) _ (fun d hd => by
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 hd
    exact pr_lt inv w q) q (by simpa using hq)]
  simp only [List.getElem_map, List.getElem_range]

def Good (P : ℕ → Prop) (a b : ℕ) : Prop := ∀ f, a ≤ f → f < b → P f

def RunOk (P : ℕ → Prop) (a b : ℕ) : Prop := bad ≤ b ∨ (a ≤ b ∧ Good P a b)

theorem RunOk.refl (P : ℕ → Prop) (a : ℕ) : RunOk P a a :=
  Or.inr ⟨le_rfl, fun _ h1 h2 => absurd h2 (by omega)⟩

theorem RunOk.trans {P : ℕ → Prop} {a b c : ℕ} (h1 : RunOk P a b) (h2 : RunOk P b c) :
    RunOk P a c := by
  rcases h1 with h1 | ⟨hab, g1⟩
  · rcases h2 with h2 | ⟨hbc, -⟩
    · exact Or.inl h2
    · exact Or.inl (le_trans h1 hbc)
  · rcases h2 with h2 | ⟨hbc, g2⟩
    · exact Or.inl h2
    · refine Or.inr ⟨le_trans hab hbc, fun f hf1 hf2 => ?_⟩
      rcases lt_or_ge f b with hf | hf
      · exact g1 f hf1 hf
      · exact g2 f hf hf2

theorem RunOk.good {P : ℕ → Prop} {a b : ℕ} (h : RunOk P a b) (hb : b < bad) :
    ∀ f, a ≤ f → f < b → P f := by
  rcases h with h | ⟨-, h⟩
  · exact absurd h (by omega)
  · exact h

theorem iter_run {P : ℕ → Prop} (step : ℕ × ℕ → ℕ × ℕ)
    (hstep : ∀ st : ℕ × ℕ, (step st).2 = bad ∨ ((step st).2 = st.2 + 1 ∧ P st.2)) :
    ∀ (k : ℕ) (init : ℕ × ℕ),
      RunOk P init.2 (Nat.rec (motive := fun _ => ℕ × ℕ) init (fun _ st => step st) k).2 := by
  intro k init
  induction k with
  | zero => exact RunOk.refl P _
  | succ k ih =>
    refine ih.trans ?_
    rcases hstep (Nat.rec (motive := fun _ => ℕ × ℕ) init (fun _ st => step st) k) with h | ⟨h, hp⟩
    · exact Or.inl (by rw [Nat.rec_add_one, h])
    · rw [Nat.rec_add_one, h]
      refine Or.inr ⟨by omega, fun f hf1 hf2 => ?_⟩
      have : f = (Nat.rec (motive := fun _ => ℕ × ℕ) init (fun _ st => step st) k).2 := by omega
      rw [this]
      exact hp

theorem list_run {P : ℕ → Prop} (elem : ℕ → ℕ → ℕ) (helem : ∀ E f, RunOk P f (elem E f)) :
    ∀ (l : List ℕ) (f : ℕ),
      RunOk P f (List.rec (motive := fun _ => ℕ → ℕ) (fun f => f)
        (fun E _ ih f => ih (elem E f)) l f) := by
  intro l
  induction l with
  | nil => exact fun f => RunOk.refl P f
  | cons E l ih => exact fun f => (helem E f).trans (ih (elem E f))

theorem rX_lt (e : ℕ) : rX e < 2 ^ 28 := by
  unfold rX
  change e &&& (2 ^ 28 - 1) < _
  rw [land_mask]
  exact Nat.mod_lt _ (by positivity)

theorem rX_ne_bad (e : ℕ) : rX e ≠ bad := by
  intro h
  have := rX_lt e
  rw [h] at this
  exact absurd this (by unfold bad; norm_num)

theorem fwd_spec {e a cur : ℕ} (h : fwd e a cur ≠ bad) :
    rX e = cur ∧ rC e = a ∧ fwd e a cur = rY e := by
  unfold fwd at h ⊢
  cases h1 : Nat.beq (rX e) cur <;> cases h2 : Nat.beq (rC e) a <;>
    simp only [h1, h2, andB] at h ⊢
  all_goals first
    | exact absurd rfl h
    | exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, trivial⟩

theorem bwd_spec {e ai cur : ℕ} (h : bwd e ai cur ≠ bad) :
    rY e = cur ∧ rC e = ai ∧ bwd e ai cur = rX e := by
  unfold bwd at h ⊢
  cases h1 : Nat.beq (rY e) cur <;> cases h2 : Nat.beq (rC e) ai <;>
    simp only [h1, h2, andB] at h ⊢
  all_goals first
    | exact absurd rfl h
    | exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, trivial⟩

theorem fwd_bad (e a : ℕ) : fwd e a bad = bad := by
  by_contra h
  exact rX_ne_bad e (fwd_spec h).1

theorem bwd_bad {e : ℕ} (ai : ℕ) (he : rY e ≠ bad) : bwd e ai bad = bad := by
  by_contra h
  exact he (bwd_spec h).1

def rel {G : Type*} [Group G] (H : Subgroup G) (u v : G) : Prop := u * v⁻¹ ∈ H

theorem rel_refl {G : Type*} [Group G] (H : Subgroup G) (u : G) : rel H u u := by
  rw [rel, mul_inv_cancel]
  exact H.one_mem

theorem rel_symm {G : Type*} [Group G] {H : Subgroup G} {u v : G} (h : rel H u v) : rel H v u := by
  have := H.inv_mem h
  rwa [mul_inv_rev, inv_inv] at this

theorem rel_trans {G : Type*} [Group G] {H : Subgroup G} {u v w : G} (h1 : rel H u v)
    (h2 : rel H v w) : rel H u w := by
  have := H.mul_mem h1 h2
  rwa [mul_assoc, inv_mul_cancel_left] at this

theorem rel_mul_right {G : Type*} [Group G] {H : Subgroup G} {u v : G} (x : G) (h : rel H u v) :
    rel H (u * x) (v * x) := by
  unfold rel at h ⊢
  rwa [mul_inv_rev, mul_assoc, mul_inv_cancel_left]

def Holds {G : Type*} [Group G] (H : Subgroup G) (val rep : ℕ → G) (e : ℕ) : Prop :=
  rel H (rep (rX e) * val (rC e)) (rep (rY e))

theorem walk_sound {G : Type*} [Group G] (H : Subgroup G) (val rep : ℕ → G) (F : ℕ → ℕ)
    (RW RM f own t wd refs s n : ℕ) (a ai : ℕ → ℕ)
    (ha : ∀ q < n, Nat.land (Nat.shiftRight wd
      (Nat.add (nat_lit 24) (Nat.shiftLeft q (nat_lit 4)))) (nat_lit 255) = a q)
    (hai : ∀ q < n, Nat.shiftRight (Nat.land (Nat.shiftRight wd
      (Nat.add (nat_lit 24) (Nat.shiftLeft q (nat_lit 4)))) (nat_lit 65535)) (nat_lit 8) = ai q)
    (hinv : ∀ q < n, val (ai q) = (val (a q))⁻¹)
    (hfacts : ∀ g < f, Holds H val rep (F g) ∧ rY (F g) ≠ bad)
    (hword : rel H (rep s * lv val ((List.range n).map a)) (rep s))
    (hs : s ≠ bad) (ht : t < n)
    (hend : Nat.rec (motive := fun _ => ℕ) s (fun q cur => vStep F RW RM f own t wd refs q cur)
      n = s) :
    Holds H val rep own ∧ rY own ≠ bad := by
  set cur : ℕ → ℕ := fun k =>
    Nat.rec (motive := fun _ => ℕ) s (fun q cur => vStep F RW RM f own t wd refs q cur) k with hcur
  have hcur0 : cur 0 = s := rfl
  have hcurS : ∀ q, cur (q + 1) = vStep F RW RM f own t wd refs q (cur q) := fun q => rfl
  have hp255 : ∀ q < n, Nat.land (Nat.land (Nat.shiftRight wd
      (Nat.add (nat_lit 24) (Nat.shiftLeft q (nat_lit 4)))) (nat_lit 65535)) (nat_lit 255) = a q := by
    intro q hq
    rw [← ha q hq]
    change (_ &&& 65535) &&& 255 = _ &&& 255
    rw [Nat.and_assoc]
    rfl
  have hstepbad : ∀ q, vStep F RW RM f own t wd refs q bad = bad := by
    intro q
    unfold vStep
    cases hq : Nat.beq q t
    · unfold vRef
      dsimp only
      cases hg : Nat.ble f (Nat.shiftRight (Nat.land (Nat.shiftRight refs (Nat.mul RW q)) RM)
        (nat_lit 1))
      · have hlt : Nat.shiftRight (Nat.land (Nat.shiftRight refs (Nat.mul RW q)) RM)
            (nat_lit 1) < f := ble_false hg
        cases Nat.beq (Nat.land (Nat.land (Nat.shiftRight refs (Nat.mul RW q)) RM) (nat_lit 1))
          (nat_lit 1)
        · exact fwd_bad _ _
        · exact bwd_bad _ (hfacts _ hlt).2
      · rfl
    · exact fwd_bad _ _
  have hne : ∀ q ≤ n, cur q ≠ bad := by
    intro q hq hb
    have : ∀ k, cur (q + k) = bad := by
      intro k
      induction k with
      | zero => exact hb
      | succ k ih => rw [← add_assoc, hcurS, ih, hstepbad]
    have := this (n - q)
    rw [Nat.add_sub_cancel' hq] at this
    exact hs (hend.symm.trans this)
  have hstep : ∀ q < n, q ≠ t → rel H (rep (cur q) * val (a q)) (rep (cur (q + 1))) := by
    intro q hq hqt
    have hn := hne (q + 1) hq
    rw [hcurS] at hn ⊢
    unfold vStep at hn ⊢
    have hbeq : Nat.beq q t = false := beq_false_of_ne hqt
    rw [hbeq] at hn ⊢
    dsimp only at hn ⊢
    unfold vRef at hn ⊢
    set r := Nat.land (Nat.shiftRight refs (Nat.mul RW q)) RM
    cases hg : Nat.ble f (Nat.shiftRight r (nat_lit 1))
    · simp only [hg] at hn ⊢
      have hlt : Nat.shiftRight r (nat_lit 1) < f := ble_false hg
      obtain ⟨hH, -⟩ := hfacts _ hlt
      cases hd : Nat.beq (Nat.land r (nat_lit 1)) (nat_lit 1)
      · simp only [hd] at hn ⊢
        change fwd _ _ _ ≠ bad at hn
        change rel H _ (rep (fwd _ _ _))
        obtain ⟨h1, h2, h3⟩ := fwd_spec hn
        rw [h3]
        unfold Holds at hH
        rwa [h1, h2, hp255 q hq] at hH
      · simp only [hd] at hn ⊢
        change bwd _ _ _ ≠ bad at hn
        change rel H _ (rep (bwd _ _ _))
        obtain ⟨h1, h2, h3⟩ := bwd_spec hn
        rw [h3]
        unfold Holds at hH
        rw [h1, h2, hai q hq, hinv q hq] at hH
        have := rel_mul_right (val (a q)) (rel_symm hH)
        rwa [inv_mul_cancel_right] at this
    · simp only [hg] at hn
      exact absurd rfl hn
  have hown : rX own = cur t ∧ rC own = a t ∧ cur (t + 1) = rY own := by
    have hn := hne (t + 1) ht
    rw [hcurS] at hn ⊢
    unfold vStep at hn ⊢
    have hbeq : Nat.beq t t = true := Nat.beq_refl t
    rw [hbeq] at hn ⊢
    dsimp only at hn ⊢
    change fwd _ _ _ ≠ bad at hn
    change _ ∧ _ ∧ fwd _ _ _ = _
    obtain ⟨h1, h2, h3⟩ := fwd_spec hn
    exact ⟨h1, h2.trans (ha t ht), h3⟩
  set W : ℕ → G := fun k => lv val ((List.range k).map a) with hW
  have hWS : ∀ k, W (k + 1) = W k * val (a k) := by
    intro k
    simp only [hW, List.range_succ, List.map_append, List.map_singleton, lv_append, lv_singleton]
  have hY : ∀ q < n, q ≠ t →
      rel H (rep (cur q) * (W q)⁻¹) (rep (cur (q + 1)) * (W (q + 1))⁻¹) := by
    intro q hq hqt
    have := rel_mul_right ((W (q + 1))⁻¹) (hstep q hq hqt)
    have e : rep (cur q) * val (a q) * (W (q + 1))⁻¹ = rep (cur q) * (W q)⁻¹ := by
      rw [hWS]
      group
    rwa [e] at this
  have hpre : ∀ q ≤ t, rel H (rep s) (rep (cur q) * (W q)⁻¹) := by
    intro q hq
    induction q with
    | zero =>
      simp only [hcur0, hW, List.range_zero, List.map_nil, lv_nil, inv_one, mul_one]
      exact rel_refl H _
    | succ q ih => exact rel_trans (ih (by omega)) (hY q (by omega) (by omega))
  have hsuf : ∀ k, t + 1 + k ≤ n →
      rel H (rep (cur (t + 1)) * (W (t + 1))⁻¹) (rep (cur (t + 1 + k)) * (W (t + 1 + k))⁻¹) := by
    intro k hk
    induction k with
    | zero => exact rel_refl H _
    | succ k ih =>
      exact rel_trans (ih (by omega)) (by
        rw [← add_assoc]
        exact hY _ (by omega) (by omega))
  have hfin := hsuf (n - (t + 1)) (by omega)
  rw [Nat.add_sub_cancel' (by omega : t + 1 ≤ n)] at hfin
  have hcn : cur n = s := hend
  rw [hcn] at hfin
  have hw' : rel H (rep s) (rep s * (W n)⁻¹) := by
    have := rel_mul_right ((W n)⁻¹) hword
    rwa [mul_inv_cancel_right] at this
  have hkey : rel H (rep (cur t) * (W t)⁻¹) (rep (cur (t + 1)) * (W (t + 1))⁻¹) :=
    rel_trans (rel_symm (hpre t le_rfl)) (rel_trans hw' (rel_symm hfin))
  have hfact : rel H (rep (cur t) * val (a t)) (rep (cur (t + 1))) := by
    have := rel_mul_right (W (t + 1)) hkey
    have e : rep (cur t) * (W t)⁻¹ * W (t + 1) = rep (cur t) * val (a t) := by
      rw [hWS]
      group
    rwa [inv_mul_cancel_right, e] at this
  obtain ⟨h1, h2, h3⟩ := hown
  refine ⟨?_, ?_⟩
  · unfold Holds
    rw [h1, h2, ← h3]
    exact hfact
  · rw [← h3]
    exact hne (t + 1) ht

theorem natrec_all (P : ℕ → Bool) : ∀ n, Nat.rec (motive := fun _ => Bool) true
    (fun c acc => Bool.rec false acc (P c)) n = true → ∀ c < n, P c = true := by
  intro n
  induction n with
  | zero => exact fun _ c hc => absurd hc (Nat.not_lt_zero c)
  | succ n ih =>
    intro h c hc
    change Bool.rec false (Nat.rec (motive := fun _ => Bool) true
      (fun c acc => Bool.rec false acc (P c)) n) (P n) = true at h
    cases hp : P n
    · rw [hp] at h
      exact absurd h Bool.false_ne_true
    · rw [hp] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
      · exact ih h c hc
      · exact hp

theorem natrec_andB (P : ℕ → Bool) : ∀ n, Nat.rec (motive := fun _ => Bool) true
    (fun c acc => andB (P c) acc) n = true → ∀ c < n, P c = true := by
  intro n
  induction n with
  | zero => exact fun _ c hc => absurd hc (Nat.not_lt_zero c)
  | succ n ih =>
    intro h c hc
    rw [Nat.rec_add_one] at h
    obtain ⟨h1, h2⟩ := andB_true_iff.1 h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
    · exact ih h2 c hc
    · exact h1

theorem natrec_all2 (P Q : ℕ → Bool) : ∀ n, Nat.rec (motive := fun _ => Bool) true
    (fun c acc => Bool.rec false (Bool.rec false acc (Q c)) (P c)) n = true →
    ∀ c < n, P c = true ∧ Q c = true := by
  intro n
  induction n with
  | zero => exact fun _ c hc => absurd hc (Nat.not_lt_zero c)
  | succ n ih =>
    intro h c hc
    change Bool.rec false (Bool.rec false (Nat.rec (motive := fun _ => Bool) true
      (fun c acc => Bool.rec false (Bool.rec false acc (Q c)) (P c)) n) (Q n)) (P n) = true at h
    cases hp : P n <;> cases hq : Q n <;> rw [hp, hq] at h
    all_goals try exact absurd h Bool.false_ne_true
    rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
    · exact ih h c hc
    · exact ⟨hp, hq⟩

def WalkP (F Wd2 : ℕ → ℕ) (RW RM nCos nW : ℕ) (f : ℕ) : Prop :=
  ∃ s t j refs, j < nW ∧ vWalkOk F RW RM nCos f (F f) s t (Wd2 j) refs = true

theorem wFactStep_spec (F Wd2 : ℕ → ℕ) (RW RM nCos nW : ℕ) (st : ℕ × ℕ) :
    (wFactStep F Wd2 RW RM nCos nW st).2 = bad ∨
      ((wFactStep F Wd2 RW RM nCos nW st).2 = st.2 + 1 ∧ WalkP F Wd2 RW RM nCos nW st.2) := by
  obtain ⟨rest, f⟩ := st
  unfold wFactStep wFactNext vFactNext
  dsimp only
  cases hj : Nat.ble (Nat.succ (Nat.land (Nat.shiftRight rest (nat_lit 36)) (nat_lit 65535))) nW
  · exact Or.inl rfl
  · cases hv : vWalkOk F RW RM nCos f (F f) (Nat.land rest (nat_lit 268435455))
        (Nat.land (Nat.shiftRight rest (nat_lit 28)) (nat_lit 255))
        (Wd2 (Nat.land (Nat.shiftRight rest (nat_lit 36)) (nat_lit 65535)))
        (Nat.shiftRight rest (nat_lit 52))
    · exact Or.inl rfl
    · exact Or.inr ⟨rfl, _, _, _, _, Nat.le_of_ble_eq_true hj, hv⟩

theorem wWalkList_run (F Wd2 : ℕ → ℕ) (RW RM nCos nW : ℕ) (l : List ℕ) (f : ℕ) :
    RunOk (WalkP F Wd2 RW RM nCos nW) f (wWalkList F Wd2 RW RM nCos nW l f) := by
  unfold wWalkList
  refine list_run _ (fun E f => ?_) l f
  unfold wElem
  exact iter_run _ (wFactStep_spec F Wd2 RW RM nCos nW) _ (Prod.mk (Nat.shiftRight E (nat_lit 8)) f)

theorem vWalkOk_spec {F : ℕ → ℕ} {RW RM nCos f own s t wd refs : ℕ}
    (h : vWalkOk F RW RM nCos f own s t wd refs = true) :
    s < nCos ∧ t < Nat.land wd (nat_lit 255) ∧
      (Nat.land (Nat.shiftRight wd (nat_lit 8)) (nat_lit 1) = 0 ∨ s = 0) ∧
      Nat.rec (motive := fun _ => ℕ) s (fun q cur => vStep F RW RM f own t wd refs q cur)
        (Nat.land wd (nat_lit 255)) = s := by
  have e : vWalkOk F RW RM nCos f own s t wd refs =
      andB (andB (Nat.ble (Nat.succ s) nCos) (Nat.ble (Nat.succ t) (Nat.land wd (nat_lit 255))))
        (andB (Nat.beq (Nat.rec (motive := fun _ => ℕ) s
            (fun q cur => vStep F RW RM f own t wd refs q cur) (Nat.land wd (nat_lit 255))) s)
          (orB (Nat.beq (Nat.land (Nat.shiftRight wd (nat_lit 8)) (nat_lit 1)) (nat_lit 0))
            (Nat.beq s (nat_lit 0)))) := rfl
  rw [e, andB_true_iff, andB_true_iff, andB_true_iff, orB_true_iff] at h
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  refine ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2, ?_, Nat.eq_of_beq_eq_true h3⟩
  rcases h4 with h4 | h4
  · exact Or.inl (Nat.eq_of_beq_eq_true h4)
  · exact Or.inr (Nat.eq_of_beq_eq_true h4)

def CovP (F : ℕ → ℕ) (RW RM N L nF : ℕ) (x : ℕ) : Prop :=
  ∃ rest, Nat.rec (motive := fun _ => Bool) true
    (fun c acc => Bool.rec false acc
      (wCovEntry F N nF x c (Nat.land (Nat.shiftRight rest (Nat.mul RW c)) RM))) L = true

theorem wCovStep_spec (F : ℕ → ℕ) (RW RM N L nF : ℕ) (st : ℕ × ℕ) :
    (wCovStep F RW RM N L nF st).2 = bad ∨
      ((wCovStep F RW RM N L nF st).2 = st.2 + 1 ∧ CovP F RW RM N L nF st.2) := by
  obtain ⟨rest, x⟩ := st
  unfold wCovStep
  dsimp only
  cases hc : Nat.rec (motive := fun _ => Bool) true
    (fun c acc => Bool.rec false acc
      (wCovEntry F N nF x c (Nat.land (Nat.shiftRight rest (Nat.mul RW c)) RM))) L
  · exact Or.inl rfl
  · exact Or.inr ⟨rfl, rest, hc⟩

theorem wCovList_run (F : ℕ → ℕ) (RW RM N L nF : ℕ) (l : List ℕ) (x : ℕ) :
    RunOk (CovP F RW RM N L nF) x (wCovList F RW RM N L nF l x) := by
  unfold wCovList
  refine list_run _ (fun E x => ?_) l x
  unfold wCovElem
  exact iter_run _ (wCovStep_spec F RW RM N L nF) _ (Prod.mk (Nat.shiftRight E (nat_lit 8)) x)

theorem wCovEntry_spec {F : ℕ → ℕ} {N nF x c r : ℕ} (h : wCovEntry F N nF x c r = true) :
    Nat.shiftRight r (nat_lit 1) < nF ∧
      ((rY (F (Nat.shiftRight r (nat_lit 1))) = x ∧
        rC (F (Nat.shiftRight r (nat_lit 1))) = Nat.xor c 1 ∧
        rX (F (Nat.shiftRight r (nat_lit 1))) < N) ∨
      (rX (F (Nat.shiftRight r (nat_lit 1))) = x ∧ rC (F (Nat.shiftRight r (nat_lit 1))) = c ∧
        rY (F (Nat.shiftRight r (nat_lit 1))) < N)) := by
  have e : wCovEntry F N nF x c r =
      andB (Nat.ble (Nat.succ (Nat.shiftRight r (nat_lit 1))) nF)
        (Bool.rec
          (andB (Nat.beq (rX (F (Nat.shiftRight r (nat_lit 1)))) x)
            (andB (Nat.beq (rC (F (Nat.shiftRight r (nat_lit 1)))) c)
              (Nat.ble (Nat.succ (rY (F (Nat.shiftRight r (nat_lit 1))))) N)))
          (andB (Nat.beq (rY (F (Nat.shiftRight r (nat_lit 1)))) x)
            (andB (Nat.beq (rC (F (Nat.shiftRight r (nat_lit 1)))) (Nat.xor c (nat_lit 1)))
              (Nat.ble (Nat.succ (rX (F (Nat.shiftRight r (nat_lit 1))))) N)))
          (Nat.beq (Nat.land r (nat_lit 1)) (nat_lit 1))) := rfl
  rw [e, andB_true_iff] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨Nat.le_of_ble_eq_true h1, ?_⟩
  cases hd : Nat.beq (Nat.land r (nat_lit 1)) (nat_lit 1) <;> rw [hd] at h2 <;>
    simp only [andB_true_iff] at h2 <;> obtain ⟨h3, h4, h5⟩ := h2
  · exact Or.inr ⟨Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4, Nat.le_of_ble_eq_true h5⟩
  · exact Or.inl ⟨Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4, Nat.le_of_ble_eq_true h5⟩

noncomputable def repF {G : Type*} [Group G] (val : ℕ → G) (F : ℕ → ℕ) (nT : ℕ) : ℕ → ℕ → G
  | 0, _ => 1
  | d + 1, k => if 1 ≤ k ∧ k ≤ nT then repF val F nT d (rX (F (k - 1))) * val (rC (F (k - 1)))
      else 1

noncomputable def rep {G : Type*} [Group G] (val : ℕ → G) (F D : ℕ → ℕ) (nT k : ℕ) : G :=
  repF val F nT (D k) k

theorem rep_zero {G : Type*} [Group G] (val : ℕ → G) (F D : ℕ → ℕ) (nT : ℕ) :
    rep val F D nT 0 = 1 := by
  unfold rep
  cases D 0 with
  | zero => rfl
  | succ d =>
    rw [repF, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

theorem rep_tree {G : Type*} [Group G] (val : ℕ → G) (F D : ℕ → ℕ) (nT k : ℕ) (hk1 : 1 ≤ k)
    (hk2 : k ≤ nT) (hD : D k = D (rX (F (k - 1))) + 1) :
    rep val F D nT k = rep val F D nT (rX (F (k - 1))) * val (rC (F (k - 1))) := by
  unfold rep
  rw [hD, repF, ite_eq_left_of_eq_true _ _ (eq_true ⟨hk1, hk2⟩)]

theorem rep_mem {G : Type*} [Group G] (val : ℕ → G) (F D : ℕ → ℕ) (nT : ℕ) (K : Subgroup G)
    (hK : ∀ c, val c ∈ K) (k : ℕ) : rep val F D nT k ∈ K := by
  unfold rep
  generalize D k = d
  induction d generalizing k with
  | zero => exact K.one_mem
  | succ d ih =>
    rw [repF]
    split_ifs
    · exact K.mul_mem (ih _) (hK _)
    · exact K.one_mem

theorem treeRange_spec {F D : ℕ → ℕ} {L nCos cnt : ℕ} (h : treeRange F D L nCos (nat_lit 0) cnt = true)
    (i : ℕ) (hi : i < cnt) :
    rY (F i) = i + 1 ∧ rC (F i) < L ∧ rX (F i) < nCos ∧ D (i + 1) = D (rX (F i)) + 1 := by
  unfold treeRange at h
  have := natrec_andB (fun i => treeOk' D L nCos (Nat.add (nat_lit 0) (Nat.succ i))
    (F (Nat.add (nat_lit 0) i))) cnt h i hi
  simp only [Nat.add_eq, Nat.zero_add] at this
  unfold treeOk' at this
  simp only [andB_true_iff] at this
  obtain ⟨h1, h2, h3, h4⟩ := this
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.le_of_ble_eq_true h2, Nat.le_of_ble_eq_true h3,
    Nat.eq_of_beq_eq_true h4⟩

theorem shiftLeft_four (q : ℕ) : q <<< 4 = 16 * q := by
  rw [Nat.shiftLeft_eq]
  ring

theorem cover_closed {G : Type*} [Group G] (H : Subgroup G) (val : ℕ → G)
    {inv L nLab nT N RW RM nW nF : ℕ} {F D Wd Wd2 : ℕ → ℕ} {walk cov : List ℕ}
    (hNl : N ≤ nLab) (hlab : nLab = nT + 1) (hlabbad : nLab + 1 ≤ bad) (hFbad : nF + 1 ≤ bad)
    (hxor : ∀ c < L, val (Nat.xor c 1) = (val c)⁻¹)
    (hinvv : ∀ c ≤ L, val (byte inv c) = (val c)⁻¹)
    (hW : ∀ j < nW, (∀ q < wN (Wd j), letter (Wd j) q ≤ L) ∧
      (wKind (Wd j) = 0 → lv val (wbytes (Wd j)) = 1) ∧
      (wKind (Wd j) = 1 → lv val (wbytes (Wd j)) ∈ H))
    (h2 : words2Ok Wd Wd2 inv nW = true)
    (htree : treeRange F D L nLab (nat_lit 0) nT = true)
    (hwalk : wWalkList F Wd2 RW RM nLab nW walk nT = nF)
    (hcov : wCovList F RW RM N L nF cov (nat_lit 0) = N) :
    ∀ x < N, ∀ c < L, ∃ y < N, rel H (rep val F D nT x * val c) (rep val F D nT y) := by
  have hbad : bad = 4611686018427387904 := rfl
  have hpairs : ∀ j < nW, Wd2 j = pairs inv (Wd j) := by
    intro j hj
    unfold words2Ok at h2
    exact Nat.eq_of_beq_eq_true
      (natrec_all (fun j => Nat.beq (Wd2 j) (pairs inv (Wd j))) nW h2 j hj)
  have hfacts : ∀ f < nF, Holds H val (rep val F D nT) (F f) ∧ rY (F f) ≠ bad := by
    intro f
    induction f using Nat.strong_induction_on with
    | _ f ih =>
    intro hf
    rcases lt_or_ge f nT with hfT | hfT
    · obtain ⟨h1, -, -, h4⟩ := treeRange_spec htree f hfT
      refine ⟨?_, ?_⟩
      · unfold Holds
        rw [h1, rep_tree val F D nT (f + 1) (by omega) (by omega)
          (by rw [Nat.add_sub_cancel]; exact h4)]
        simp only [Nat.add_sub_cancel]
        exact rel_refl H _
      · rw [h1]
        omega
    · have hgood := (wWalkList_run F Wd2 RW RM nLab nW walk nT).good (by rw [hwalk]; omega)
      rw [hwalk] at hgood
      obtain ⟨s, t, j, refs, hj, hv⟩ := hgood f hfT hf
      obtain ⟨hs, ht, hkind, hend⟩ := vWalkOk_spec hv
      obtain ⟨hle, hk0, hk1⟩ := hW j hj
      have hwd := hpairs j hj
      have hn : Nat.land (Wd2 j) (nat_lit 255) = wN (Wd j) := by
        rw [hwd, wN_eq]
        change pairs inv (Wd j) &&& (2 ^ 8 - 1) = _
        rw [land_mask]
        exact pairs_low inv (Wd j)
      have hk : Nat.land (Nat.shiftRight (Wd2 j) (nat_lit 8)) (nat_lit 1) = wKind (Wd j) := by
        rw [hwd, wKind_eq]
        change (pairs inv (Wd j) >>> 8) &&& (2 ^ 1 - 1) = _
        rw [land_mask, Nat.shiftRight_eq_div_pow]
        exact pairs_kind inv (Wd j)
      have hpr : ∀ q < Nat.land (Wd2 j) (nat_lit 255),
          pairs inv (Wd j) / 2 ^ (24 + 16 * q) % 65536 = pr inv (Wd j) q := by
        intro q hq
        rw [hn] at hq
        exact pairs_pair inv (Wd j) q hq
      have hlet : ∀ q, letter (Wd j) q < 256 := by
        intro q
        rw [letter_eq]
        exact byte_lt _ _
      have ha : ∀ q < Nat.land (Wd2 j) (nat_lit 255), Nat.land (Nat.shiftRight (Wd2 j)
          (Nat.add (nat_lit 24) (Nat.shiftLeft q (nat_lit 4)))) (nat_lit 255) = letter (Wd j) q := by
        intro q hq
        change (Wd2 j >>> (24 + (q <<< 4))) &&& (2 ^ 8 - 1) = _
        rw [land_mask, Nat.shiftRight_eq_div_pow, shiftLeft_four, hwd,
          ← Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 8 ∣ 65536), hpr q hq, pr,
          (by norm_num : (2 : ℕ) ^ 8 = 256), Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt (hlet q)
      have hai : ∀ q < Nat.land (Wd2 j) (nat_lit 255), Nat.shiftRight (Nat.land (Nat.shiftRight
          (Wd2 j) (Nat.add (nat_lit 24) (Nat.shiftLeft q (nat_lit 4)))) (nat_lit 65535))
          (nat_lit 8) = byte inv (letter (Wd j) q) := by
        intro q hq
        change ((Wd2 j >>> (24 + (q <<< 4))) &&& (2 ^ 16 - 1)) >>> 8 = _
        rw [land_mask, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, shiftLeft_four, hwd]
        norm_num only
        rw [hpr q hq, pr, Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt (hlet q),
          zero_add]
      have hinv : ∀ q < Nat.land (Wd2 j) (nat_lit 255),
          val (byte inv (letter (Wd j) q)) = (val (letter (Wd j) q))⁻¹ := by
        intro q hq
        rw [hn] at hq
        exact hinvv _ (hle q hq)
      have hW' : lv val ((List.range (Nat.land (Wd2 j) (nat_lit 255))).map (letter (Wd j))) =
          lv val (wbytes (Wd j)) := by
        rw [hn, wbytes, bytes]
        congr 2
        funext q
        exact letter_eq _ _
      have hword : rel H (rep val F D nT s *
          lv val ((List.range (Nat.land (Wd2 j) (nat_lit 255))).map (letter (Wd j))))
          (rep val F D nT s) := by
        rw [hW']
        have hk01 : wKind (Wd j) = 0 ∨ wKind (Wd j) = 1 := by
          rw [wKind_eq]
          omega
        rcases hk01 with h0 | h1
        · rw [hk0 h0, mul_one]
          exact rel_refl H _
        · have hs0 : s = 0 := by
            rcases hkind with hkind | hkind
            · rw [hk, h1] at hkind
              exact absurd hkind one_ne_zero
            · exact hkind
          rw [hs0, rep_zero, one_mul]
          unfold rel
          rw [inv_one, mul_one]
          exact hk1 h1
      exact walk_sound H val (rep val F D nT) F RW RM f (F f) t (Wd2 j) refs s
        (Nat.land (Wd2 j) (nat_lit 255)) (letter (Wd j)) (fun q => byte inv (letter (Wd j) q))
        ha hai hinv (fun g hg => ih g hg (by omega)) hword (by omega) ht hend
  have hgood := (wCovList_run F RW RM N L nF cov 0).good (by rw [hcov]; omega)
  rw [hcov] at hgood
  intro x hx c hc
  obtain ⟨rest, hrest⟩ := hgood x (Nat.zero_le _) hx
  have he := natrec_all _ L hrest c hc
  obtain ⟨hg, hcases⟩ := wCovEntry_spec he
  obtain ⟨hH, -⟩ := hfacts _ hg
  unfold Holds at hH
  rcases hcases with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨_, h3, ?_⟩
    rw [h1, h2, hxor c hc] at hH
    have := rel_mul_right (val c) (rel_symm hH)
    rwa [inv_mul_cancel_right] at this
  · refine ⟨_, h3, ?_⟩
    rwa [h1, h2] at hH

theorem index_le {G : Type*} [Group G] {H A : Subgroup G} (val rp : ℕ → G) {L N : ℕ}
    (hA : A ≤ Subgroup.closure (val '' {c | c < L})) (hrpA : ∀ x, rp x ∈ A)
    (hrp0 : rp 0 = 1) (hN : 1 ≤ N) (hxor : ∀ c < L, ∃ c' < L, val c' = (val c)⁻¹)
    (hcl : ∀ x < N, ∀ c < L, ∃ y < N, rel H (rp x * val c) (rp y)) :
    H.relIndex A ≠ 0 ∧ H.relIndex A ≤ N := by
  have hT : ∀ a ∈ Subgroup.closure (val '' {c | c < L}), ∃ x < N, rel H a (rp x) := by
    intro a ha
    induction ha using Subgroup.closure_induction_right with
    | one => exact ⟨0, hN, by rw [hrp0]; exact rel_refl H 1⟩
    | mul_right x hx y hy ih =>
      obtain ⟨c, hc, rfl⟩ := hy
      obtain ⟨z, hz, hr⟩ := ih
      obtain ⟨y', hy', hr'⟩ := hcl z hz c hc
      exact ⟨y', hy', rel_trans (rel_mul_right _ hr) hr'⟩
    | mul_inv_cancel x hx y hy ih =>
      obtain ⟨c, hc, rfl⟩ := hy
      obtain ⟨c', hc', hv⟩ := hxor c hc
      obtain ⟨z, hz, hr⟩ := ih
      obtain ⟨y', hy', hr'⟩ := hcl z hz c' hc'
      rw [← hv]
      exact ⟨y', hy', rel_trans (rel_mul_right _ hr) hr'⟩
  let φ : Fin N → A ⧸ H.subgroupOf A := fun x =>
    QuotientGroup.mk (⟨(rp x)⁻¹, A.inv_mem (hrpA x)⟩ : A)
  have hsurj : Function.Surjective φ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      obtain ⟨x, hx, hr⟩ := hT (a : G)⁻¹ (hA (A.inv_mem a.2))
      refine ⟨⟨x, hx⟩, ?_⟩
      change QuotientGroup.mk _ = QuotientGroup.mk _
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have := H.inv_mem hr
      simpa [mul_inv_rev] using this
  have hfin : Finite (A ⧸ H.subgroupOf A) := Finite.of_surjective φ hsurj
  refine ⟨Subgroup.index_ne_zero_of_finite, ?_⟩
  have := Nat.card_le_card_of_surjective φ hsurj
  rw [Nat.card_fin] at this
  exact this

theorem word_sem {G : Type*} [Group G] (H : Subgroup G) (val : ℕ → G) {R S : ℕ → ℕ}
    {inv eps nR nS wd : ℕ} (heps : eps < 128) (hv1 : val eps = 1)
    (hinvv : ∀ c < eps, val (byte inv c) = (val c)⁻¹)
    (hR : ∀ i < nR, wLetters (R i) = pkb 256 (wbytes (R i)) ∧ lv val (wbytes (R i)) = 1)
    (hS : ∀ i < nS, lv val (wbytes (S i)) ∈ H)
    (hok : wordOkB R S inv eps nR nS wd = true) (hle : lettersLe eps wd = true) :
    (∀ q < wN wd, letter wd q ≤ eps) ∧ (wKind wd = 0 → lv val (wbytes wd) = 1) ∧
      (wKind wd = 1 → lv val (wbytes wd) ∈ H) := by
  have hlet : ∀ q < wN wd, letter wd q ≤ eps := by
    intro q hq
    unfold lettersLe at hle
    exact Nat.le_of_ble_eq_true (natrec_all (fun q => Nat.ble (letter wd q) eps) (wN wd) hle q hq)
  refine ⟨hlet, ?_⟩
  set l' := (wbytes wd).filter (· ≠ eps) with hl'
  have hval : lv val (wbytes wd) = lv val l' := (lv_filter val eps hv1 _).symm
  have hl'lt : ∀ d ∈ l', d < eps := by
    intro d hd
    rw [hl', List.mem_filter] at hd
    obtain ⟨hd1, hd2⟩ := hd
    obtain ⟨q, hq, rfl⟩ := mem_bytes.1 hd1
    have := hlet q hq
    rw [letter_eq] at this
    have hne : byte (wLetters wd) q ≠ eps := by simpa using hd2
    omega
  have hl'256 : ∀ d ∈ l', d < 256 := fun d hd => by
    have := hl'lt d hd
    omega
  have hs : strip eps (wLetters wd) (wN wd) = (pkb 256 l', l'.length) := strip_spec _ _ _
  have hbl : bytes (pkb 256 l') l'.length = l' := bytes_pkb l' hl'256
  unfold wordOkB at hok
  rw [hs] at hok
  unfold wordOkB' at hok
  dsimp only at hok
  cases hk : Nat.beq (wKind wd) (nat_lit 1)
  · rw [hk] at hok
    have hk1 : wKind wd ≠ 1 := Nat.ne_of_beq_eq_false hk
    refine ⟨fun _ => ?_, fun h => absurd h hk1⟩
    rw [hval]
    rcases orB_true_iff.1 hok with h0 | hrot
    · have h0' := Nat.eq_of_beq_eq_true h0
      have := freeRed_one val inv (pkb 256 l') l'.length
        (fun q hq => by
          rw [byte_pkb l' hl'256 q hq]
          have := hl'lt _ (List.getElem_mem hq)
          omega)
        (fun q hq => by
          rw [byte_pkb l' hl'256 q hq]
          exact hinvv _ (hl'lt _ (List.getElem_mem hq))) h0'
      rwa [hbl] at this
    · obtain ⟨hb, hrest⟩ := andB_true_iff.1 hrot
      obtain ⟨hn, hr⟩ := andB_true_iff.1 hrest
      have hb' : wBase wd < nR := Nat.le_of_ble_eq_true hb
      have hn' : wN (R (wBase wd)) = l'.length := Nat.eq_of_beq_eq_true hn
      obtain ⟨hRl, hR1⟩ := hR _ hb'
      obtain ⟨s, -, hsr⟩ := isRot_spec hr
      set rl := wbytes (R (wBase wd)) with hrl
      have hrllen : rl.length = l'.length := by
        rw [hrl, wbytes, bytes_length, hn']
      rw [hRl, ← hrllen, rot_pkb rl (bytes_lt _ _) s] at hsr
      have heq : l' = rl.drop s ++ rl.take s := by
        have h1 := bytes_pkb (rl.drop s ++ rl.take s) (fun d hd => by
          rcases List.mem_append.1 hd with hd | hd
          · exact bytes_lt _ _ d (List.mem_of_mem_drop hd)
          · exact bytes_lt _ _ d (List.mem_of_mem_take hd))
        have hlen : (rl.drop s ++ rl.take s).length = l'.length := by
          rw [List.length_append, List.length_drop, List.length_take, ← hrllen]
          omega
        rw [hsr, hlen, hbl] at h1
        exact h1
      rw [heq]
      exact lv_rotate val rl s hR1
  · rw [hk] at hok
    have hk1 : wKind wd = 1 := Nat.eq_of_beq_eq_true hk
    refine ⟨fun h => absurd (h.symm.trans hk1) zero_ne_one, fun _ => ?_⟩
    obtain ⟨hb, hrest⟩ := andB_true_iff.1 hok
    obtain ⟨hn, hv⟩ := andB_true_iff.1 hrest
    have hb' : wBase wd < nS := Nat.le_of_ble_eq_true hb
    have hSb := hS _ hb'
    rw [wbytes, Nat.eq_of_beq_eq_true hn, Nat.eq_of_beq_eq_true hv, hbl] at hSb
    rw [hval]
    exact hSb

theorem bool_rec_eq {α : Sort*} (x y : α) (b : Bool) :
    Bool.rec (motive := fun _ => α) x y b = if b = true then y else x := by
  cases b <;> rfl

theorem sCode_eq (amap g : ℕ) (b : Bool) : sCode amap (g, b) =
    if g < 256 ∧ byte amap g ≠ 0 then 2 * (byte amap g - 1) + (if b = true then 0 else 1)
    else bad := by
  unfold sCode
  dsimp only
  have hs : Nat.shiftLeft (Nat.sub (byte amap g) (nat_lit 1)) (nat_lit 1) = 2 * (byte amap g - 1) := by
    change (byte amap g - 1) <<< 1 = _
    rw [Nat.shiftLeft_eq]
    ring
  rw [hs]
  simp only [bool_rec_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq]
  split_ifs <;> omega

theorem sCode_lt {amap : ℕ} {x : ℕ × Bool} (h : sCode amap x < 256) :
    x.1 < 256 ∧ byte amap x.1 ≠ 0 := by
  obtain ⟨g, b⟩ := x
  by_cases h1 : g < 256 ∧ byte amap g ≠ 0
  · exact h1
  · rw [sCode_eq, ite_eq_right_of_eq_false _ _ (eq_false h1)] at h
    exact absurd h (by unfold bad; norm_num)

noncomputable def sEncAux (amap : ℕ) (w : List (ℕ × Bool)) : (ℕ × ℕ) × Bool :=
  List.rec (motive := fun _ => (Nat × Nat) × Bool)
    (Prod.mk (Prod.mk (nat_lit 0) (nat_lit 0)) true)
    (fun x _ ih => Prod.rec (motive := fun _ => (Nat × Nat) × Bool) (fun v ok =>
      Prod.rec (motive := fun _ => (Nat × Nat) × Bool) (fun letters n =>
        Prod.mk
          (Prod.mk (Nat.lor (Nat.shiftLeft letters (nat_lit 8)) (sCode amap x)) (Nat.succ n))
          (Bool.rec false ok (Nat.ble (Nat.succ (sCode amap x)) (nat_lit 256)))) v) ih)
    w

theorem sEncAux_spec (amap : ℕ) : ∀ w : List (ℕ × Bool),
    (sEncAux amap w).1.2 = w.length ∧ ((sEncAux amap w).2 = true ↔ ∀ x ∈ w, sCode amap x < 256) ∧
      ((sEncAux amap w).2 = true → (sEncAux amap w).1.1 = pkb 256 (w.map (sCode amap)))
  | [] => ⟨rfl, by simp [sEncAux], fun _ => rfl⟩
  | x :: w => by
    obtain ⟨ih1, ih2, ih3⟩ := sEncAux_spec amap w
    have e : sEncAux amap (x :: w) = Prod.rec (motive := fun _ => (Nat × Nat) × Bool) (fun v ok =>
        Prod.rec (motive := fun _ => (Nat × Nat) × Bool) (fun letters n =>
          Prod.mk
            (Prod.mk (Nat.lor (Nat.shiftLeft letters (nat_lit 8)) (sCode amap x)) (Nat.succ n))
            (Bool.rec false ok (Nat.ble (Nat.succ (sCode amap x)) (nat_lit 256)))) v)
        (sEncAux amap w) := rfl
    rw [e]
    rcases hp : sEncAux amap w with ⟨⟨letters, n⟩, ok⟩
    rw [hp] at ih1 ih2 ih3
    dsimp only at ih1 ih2 ih3 ⊢
    refine ⟨by rw [ih1]; rfl, ?_, ?_⟩
    · cases hb : Nat.ble (Nat.succ (sCode amap x)) (nat_lit 256)
      · have hx : ¬ sCode amap x < 256 := fun h' => by
          rw [Nat.ble_eq_true_of_le h'] at hb
          exact Bool.noConfusion hb
        exact ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd (h x (by simp)) hx⟩
      · have hx : sCode amap x < 256 := Nat.le_of_ble_eq_true hb
        change ok = true ↔ _
        rw [ih2]
        constructor
        · intro h y hy
          rcases List.mem_cons.1 hy with rfl | hy
          · exact hx
          · exact h y hy
        · exact fun h y hy => h y (by simp [hy])
    · cases hb : Nat.ble (Nat.succ (sCode amap x)) (nat_lit 256)
      · exact fun h => absurd h Bool.false_ne_true
      · intro h
        have hx : sCode amap x < 256 := Nat.le_of_ble_eq_true hb
        change Nat.lor (Nat.shiftLeft letters (nat_lit 8)) (sCode amap x) = _
        rw [ih3 h, List.map_cons, pkb_cons]
        change pkb 256 (w.map (sCode amap)) <<< 8 ||| sCode amap x = _
        rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega : sCode amap x < 2 ^ 8), Nat.shiftLeft_eq]
        ring

theorem sEnc_eq_aux (amap : ℕ) (w : List (ℕ × Bool)) : sEnc amap w =
    (Nat.lor (sEncAux amap w).1.2 (Nat.shiftLeft (sEncAux amap w).1.1 (nat_lit 24)),
      (sEncAux amap w).2) := by
  unfold sEnc
  rfl

theorem sEnc_spec (amap : ℕ) (w : List (ℕ × Bool)) (hlen : w.length < 2 ^ 24) :
    ((sEnc amap w).2 = true ↔ ∀ x ∈ w, sCode amap x < 256) ∧
      ((sEnc amap w).2 = true →
        (sEnc amap w).1 = w.length + 2 ^ 24 * pkb 256 (w.map (sCode amap))) := by
  obtain ⟨h1, h2, h3⟩ := sEncAux_spec amap w
  rw [sEnc_eq_aux]
  refine ⟨h2, fun h => ?_⟩
  dsimp only at h ⊢
  rw [h3 h, h1]
  change w.length ||| (pkb 256 (w.map (sCode amap)) <<< 24) = _
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hlen, Nat.shiftLeft_eq]
  ring

theorem entry_wN (n P : ℕ) (hn : n < 256) : wN (n + 2 ^ 24 * P) = n := by
  rw [wN_eq]
  have h : (2 : ℕ) ^ 24 = 256 * 2 ^ 16 := by norm_num
  rw [h, mul_assoc, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hn]

theorem entry_wN_lor (n P : ℕ) (hn : n < 256) : wN ((n + 256) + 2 ^ 24 * P) = n := by
  rw [wN_eq]
  have h : (2 : ℕ) ^ 24 = 256 * 2 ^ 16 := by norm_num
  rw [h, mul_assoc, Nat.add_mul_mod_self_left, Nat.add_mod_right, Nat.mod_eq_of_lt hn]

theorem entry_wLetters (n P : ℕ) (hn : n < 2 ^ 24) : wLetters (n + 2 ^ 24 * P) = P := by
  rw [wLetters_eq, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hn, zero_add]

theorem entry_lor (n P : ℕ) (hn : n < 256) :
    Nat.lor (n + 2 ^ 24 * P) (nat_lit 256) = (n + 256) + 2 ^ 24 * P := by
  change (n + 2 ^ 24 * P) ||| 256 = _
  have h1 : n + 2 ^ 24 * P = P <<< 24 ||| n := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega : n < 2 ^ 24), Nat.shiftLeft_eq]
    ring
  have h2 : n ||| 256 = n + 256 := by
    have : (256 : ℕ) = 1 <<< 8 := rfl
    rw [this, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by omega : n < 2 ^ 8), Nat.shiftLeft_eq]
    ring
  rw [h1, Nat.or_assoc, h2, ← Nat.shiftLeft_add_eq_or_of_lt (by omega : n + 256 < 2 ^ 24),
    Nat.shiftLeft_eq]
  ring

theorem RunOk.mono {P Q : ℕ → Prop} (hPQ : ∀ i, P i → Q i) {a b : ℕ} (h : RunOk P a b) :
    RunOk Q a b := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, fun f hf1 hf2 => hPQ f (h2 f hf1 hf2)⟩

theorem RunOk.from_bad {P : ℕ → Prop} {b : ℕ} (h : RunOk P bad b) : bad ≤ b := by
  rcases h with h | ⟨h, -⟩
  · exact h
  · exact h

theorem relsOk_run (R : ℕ → ℕ) (amap : ℕ) : ∀ (rels : List (List (ℕ × Bool))) (j : ℕ),
    RunOk (fun i => ∃ r ∈ rels, (sEnc amap r).2 = true ∧ R i = (sEnc amap r).1) j
      (List.rec (motive := fun _ => Nat → Nat) (fun j => j)
        (fun r _ ih j => Prod.rec (motive := fun _ => Nat) (fun e ok =>
          Bool.rec (ih j) (Bool.rec (ih bad) (ih (Nat.succ j)) (Nat.beq (R j) e)) ok)
          (sEnc amap r)) rels j)
  | [], j => RunOk.refl _ j
  | r :: rels, j => by
    have ih := relsOk_run R amap rels
    have hmono : ∀ i, (∃ r' ∈ rels, (sEnc amap r').2 = true ∧ R i = (sEnc amap r').1) →
        ∃ r' ∈ r :: rels, (sEnc amap r').2 = true ∧ R i = (sEnc amap r').1 :=
      fun i ⟨r', h1, h2⟩ => ⟨r', List.mem_cons_of_mem _ h1, h2⟩
    dsimp only
    rcases hse : sEnc amap r with ⟨e, ok⟩
    dsimp only
    cases ok
    · exact (ih j).mono hmono
    · cases hb : Nat.beq (R j) e
      · exact Or.inl ((ih bad).from_bad)
      · refine RunOk.trans (b := j + 1) (Or.inr ⟨by omega, fun f hf1 hf2 => ?_⟩) ((ih _).mono hmono)
        have : f = j := by omega
        subst this
        exact ⟨r, by simp, by rw [hse], by rw [hse]; exact Nat.eq_of_beq_eq_true hb⟩

noncomputable def strictFold (enc : List (ℕ × Bool) → ℕ × Bool) (C : ℕ → ℕ → Bool)
    (ws : List (List (ℕ × Bool))) (j : ℕ) : ℕ :=
  List.rec (motive := fun _ => Nat → Nat) (fun j => j)
    (fun w _ ih j => Prod.rec (motive := fun _ => Nat) (fun e ok =>
      Bool.rec (ih bad) (Bool.rec (ih bad) (ih (Nat.succ j)) (C j e)) ok) (enc w)) ws j

theorem strictFold_cons (enc : List (ℕ × Bool) → ℕ × Bool) (C : ℕ → ℕ → Bool)
    (w : List (ℕ × Bool)) (ws : List (List (ℕ × Bool))) (j : ℕ) :
    strictFold enc C (w :: ws) j = Bool.rec (strictFold enc C ws bad)
      (Bool.rec (strictFold enc C ws bad) (strictFold enc C ws (j + 1)) (C j (enc w).1))
      (enc w).2 := by
  rfl

theorem strictFold_run (enc : List (ℕ × Bool) → ℕ × Bool) (C : ℕ → ℕ → Bool) :
    ∀ (ws : List (List (ℕ × Bool))) (j : ℕ), bad ≤ strictFold enc C ws j ∨
      (strictFold enc C ws j = j + ws.length ∧
        ∀ i (hi : i < ws.length), (enc ws[i]).2 = true ∧ C (j + i) (enc ws[i]).1 = true)
  | [], j => Or.inr ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | w :: ws, j => by
    have ih := strictFold_run enc C ws
    have hbad : bad ≤ strictFold enc C ws bad := by
      rcases ih bad with h | ⟨h, -⟩
      · exact h
      · omega
    rw [strictFold_cons]
    cases hok : (enc w).2
    · exact Or.inl hbad
    · cases hc : C j (enc w).1
      · exact Or.inl hbad
      · dsimp only
        rcases ih (j + 1) with h | ⟨h1, h3⟩
        · exact Or.inl h
        · refine Or.inr ⟨by rw [h1, List.length_cons]; omega, fun i hi => ?_⟩
          cases i with
          | zero => exact ⟨hok, hc⟩
          | succ i =>
            have := h3 i (by simpa using hi)
            rw [Nat.add_assoc, Nat.add_comm 1 i] at this
            simpa using this

theorem subsOk_spec {S : ℕ → ℕ} {nS amap : ℕ} {subs : List (List (ℕ × Bool))}
    (h : subsOk S nS amap subs = true) (hnS : nS < bad) :
    nS = subs.length ∧ ∀ i (hi : i < subs.length), (sEnc amap subs[i]).2 = true ∧
      S i = Nat.lor (sEnc amap subs[i]).1 (nat_lit 256) := by
  have e : subsOk S nS amap subs = Nat.beq (strictFold (sEnc amap)
      (fun j e => Nat.beq (S j) (Nat.lor e (nat_lit 256))) subs 0) nS := rfl
  rw [e] at h
  have h' := Nat.eq_of_beq_eq_true h
  rcases strictFold_run (sEnc amap) (fun j e => Nat.beq (S j) (Nat.lor e (nat_lit 256))) subs 0
    with h1 | ⟨h1, h2⟩
  · omega
  · refine ⟨by omega, fun i hi => ⟨(h2 i hi).1, ?_⟩⟩
    have := Nat.eq_of_beq_eq_true (h2 i hi).2
    simpa using this



noncomputable def alphaScanN (amap n : ℕ) : ℕ × ℕ :=
  Nat.rec (motive := fun _ => Nat × Nat) (Prod.mk (nat_lit 0) (nat_lit 0))
    (fun g acc => Prod.rec (motive := fun _ => Nat × Nat) (fun cnt mask =>
      Prod.mk (Bool.rec (Nat.succ cnt) cnt (Nat.beq (byte amap g) (nat_lit 0)))
        (Nat.lor mask (Nat.shiftLeft (nat_lit 1) (byte amap g)))) acc) n

theorem alphaScanN_spec (amap : ℕ) : ∀ n,
    (alphaScanN amap n).1 = ((Finset.range n).filter (fun g => byte amap g ≠ 0)).card ∧
      ∀ k, (alphaScanN amap n).2.testBit k = true ↔ ∃ g < n, byte amap g = k
  | 0 => ⟨rfl, fun k => by simp [alphaScanN]⟩
  | n + 1 => by
    obtain ⟨ih1, ih2⟩ := alphaScanN_spec amap n
    have e : alphaScanN amap (n + 1) = Prod.rec (motive := fun _ => Nat × Nat) (fun cnt mask =>
        Prod.mk (Bool.rec (Nat.succ cnt) cnt (Nat.beq (byte amap n) (nat_lit 0)))
          (Nat.lor mask (Nat.shiftLeft (nat_lit 1) (byte amap n)))) (alphaScanN amap n) := rfl
    rw [e]
    rcases hp : alphaScanN amap n with ⟨cnt, mask⟩
    rw [hp] at ih1 ih2
    dsimp only at ih1 ih2 ⊢
    refine ⟨?_, fun k => ?_⟩
    · rw [Finset.range_add_one, Finset.filter_insert, ih1]
      cases hb : Nat.beq (byte amap n) (nat_lit 0)
      · have hne : byte amap n ≠ 0 := Nat.ne_of_beq_eq_false hb
        rw [ite_eq_left_of_eq_true _ _ (eq_true hne), Finset.card_insert_of_notMem (by simp)]
      · have heq : byte amap n = 0 := Nat.eq_of_beq_eq_true hb
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by simpa using heq))]
    · change (mask ||| 1 <<< byte amap n).testBit k = true ↔ _
      rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true, ih2]
      constructor
      · rintro (⟨g, hg, h⟩ | h)
        · exact ⟨g, by omega, h⟩
        · exact ⟨n, by omega, by simpa using h⟩
      · rintro ⟨g, hg, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hg | rfl
        · exact Or.inl ⟨g, hg, h⟩
        · exact Or.inr (by simpa using h)

theorem alphaOk_spec {amap L : ℕ} (h : alphaOk amap L = true) : ∃ cnt, L = 2 * cnt ∧
    ((Finset.range 256).filter (fun g => byte amap g ≠ 0)).card = cnt ∧
    ∀ k, 1 ≤ k → k ≤ cnt → ∃ g < 256, byte amap g = k := by
  have e : alphaScan amap = alphaScanN amap 256 := rfl
  obtain ⟨h1, h2⟩ := alphaScanN_spec amap 256
  unfold alphaOk at h
  rw [e] at h
  rcases hp : alphaScanN amap 256 with ⟨cnt, mask⟩
  rw [hp] at h h1 h2
  dsimp only at h h1 h2
  have e2 : Bool.rec false (Nat.beq (Nat.lor mask (nat_lit 1))
      (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.succ cnt)) (nat_lit 1)))
      (Nat.beq (Nat.shiftLeft cnt (nat_lit 1)) L) = andB (Nat.beq (Nat.shiftLeft cnt (nat_lit 1)) L)
      (Nat.beq (Nat.lor mask (nat_lit 1))
        (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.succ cnt)) (nat_lit 1))) := rfl
  rw [e2, andB_true_iff] at h
  obtain ⟨hL, hm⟩ := h
  have hL' := Nat.eq_of_beq_eq_true hL
  have hm' := Nat.eq_of_beq_eq_true hm
  change cnt <<< 1 = L at hL'
  change mask ||| 1 = (1 <<< (cnt + 1)) - 1 at hm'
  refine ⟨cnt, by rw [← hL', Nat.shiftLeft_eq]; ring, h1.symm, fun k hk1 hk2 => ?_⟩
  have hbit : (mask ||| 1).testBit k = true := by
    rw [hm', Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]
    simpa using (by omega : k < cnt + 1)
  rw [Nat.testBit_or] at hbit
  have h1k : (1 : ℕ).testBit k = false := by
    have : (1 : ℕ) = 2 ^ 0 := rfl
    rw [this, Nat.testBit_two_pow]
    simpa using (by omega : 0 ≠ k)
  rw [h1k, Bool.or_false] at hbit
  exact (h2 k).1 hbit

theorem alpha_struct {amap cnt : ℕ}
    (hcnt : ((Finset.range 256).filter (fun g => byte amap g ≠ 0)).card = cnt)
    (hsurj : ∀ k, 1 ≤ k → k ≤ cnt → ∃ g < 256, byte amap g = k) :
    (∀ g < 256, byte amap g ≤ cnt) ∧
      ∀ g1 g2, g1 < 256 → g2 < 256 → byte amap g1 ≠ 0 → byte amap g1 = byte amap g2 → g1 = g2 := by
  set Sg := (Finset.range 256).filter (fun g => byte amap g ≠ 0) with hSg
  have hsub : Finset.Icc 1 cnt ⊆ Sg.image (byte amap) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    obtain ⟨g, hg, hgk⟩ := hsurj k hk.1 hk.2
    rw [Finset.mem_image]
    exact ⟨g, by rw [hSg, Finset.mem_filter, Finset.mem_range]; exact ⟨hg, by omega⟩, hgk⟩
  have hcard : (Sg.image (byte amap)).card ≤ (Finset.Icc 1 cnt).card := by
    rw [Nat.card_Icc]
    exact le_trans Finset.card_image_le (by omega)
  have himg := Finset.eq_of_subset_of_card_le hsub hcard
  refine ⟨fun g hg => ?_, fun g1 g2 hg1 hg2 hb1 hb12 => ?_⟩
  · by_cases hb : byte amap g = 0
    · omega
    · have : byte amap g ∈ Sg.image (byte amap) :=
        Finset.mem_image_of_mem _ (by rw [hSg, Finset.mem_filter, Finset.mem_range]; exact ⟨hg, hb⟩)
      rw [← himg, Finset.mem_Icc] at this
      exact this.2
  · have hm1 : g1 ∈ Sg := by rw [hSg, Finset.mem_filter, Finset.mem_range]; exact ⟨hg1, hb1⟩
    have hm2 : g2 ∈ Sg := by
      rw [hSg, Finset.mem_filter, Finset.mem_range]
      exact ⟨hg2, by rw [← hb12]; exact hb1⟩
    refine Finset.inj_on_of_surj_on_of_card_le (s := Sg) (t := Finset.Icc 1 cnt)
      (fun g _ => byte amap g) (fun g hg => ?_) (fun k hk => ?_) (by rw [Nat.card_Icc]; omega)
      hm1 hm2 hb12
    · rw [himg]
      exact Finset.mem_image_of_mem _ hg
    · rw [himg, Finset.mem_image] at hk
      obtain ⟨g, hg, rfl⟩ := hk
      exact ⟨g, hg, rfl⟩

theorem invOk_spec {inv L : ℕ} (h : invOk inv L = true) :
    byte inv L = L ∧ ∀ c < L, byte inv c = Nat.xor c 1 := by
  have e : invOk inv L = andB (Nat.beq (byte inv L) L) (Nat.rec (motive := fun _ => Bool) true
      (fun c acc => Bool.rec false acc (Nat.beq (byte inv c) (Nat.xor c (nat_lit 1)))) L) := rfl
  rw [e, andB_true_iff] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, fun c hc =>
    Nat.eq_of_beq_eq_true (natrec_all (fun c => Nat.beq (byte inv c) (Nat.xor c 1)) L h.2 c hc)⟩

theorem hdrOk_spec {inv L eps amap : ℕ} (h : hdrOk inv L eps amap = true) :
    eps = L ∧ invOk inv L = true ∧ alphaOk amap L = true := by
  have e : hdrOk inv L eps amap = andB (Nat.beq eps L) (andB (invOk inv L) (alphaOk amap L)) := rfl
  rw [e, andB_true_iff, andB_true_iff] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, h.2.1, h.2.2⟩

theorem linkOk_spec {amap' : ℕ} {ws : List (List (ℕ × Bool))} (h : linkOk amap' ws = true) :
    ((Finset.range 256).filter (fun g => byte amap' g ≠ 0)).card = ws.length ∧
      ∀ i (hi : i < ws.length), (sEnc amap' ws[i]).2 = true ∧
        (sEnc amap' ws[i]).1 = Nat.lor 1 (Nat.shiftLeft (Nat.shiftLeft i 1) 24) := by
  have e0 : alphaScan amap' = alphaScanN amap' 256 := rfl
  have e : linkOk amap' ws = Nat.beq (strictFold (sEnc amap')
      (fun j e => Nat.beq e (Nat.lor (nat_lit 1)
        (Nat.shiftLeft (Nat.shiftLeft j (nat_lit 1)) (nat_lit 24)))) ws 0)
        (alphaScanN amap' 256).1 := by
    unfold linkOk
    rw [e0]
    rcases alphaScanN amap' 256 with ⟨cnt, mask⟩
    rfl
  rw [e, (alphaScanN_spec amap' 256).1] at h
  have h' := Nat.eq_of_beq_eq_true h
  have hcnt : ((Finset.range 256).filter (fun g => byte amap' g ≠ 0)).card < bad := by
    have := Finset.card_le_card (Finset.filter_subset (fun g => byte amap' g ≠ 0) (Finset.range 256))
    rw [Finset.card_range] at this
    have hb : (256 : ℕ) < bad := by unfold bad; norm_num
    omega
  rcases strictFold_run (sEnc amap') (fun j e => Nat.beq e (Nat.lor (nat_lit 1)
      (Nat.shiftLeft (Nat.shiftLeft j (nat_lit 1)) (nat_lit 24)))) ws 0 with h1 | ⟨h1, h2⟩
  · omega
  · refine ⟨by omega, fun i hi => ⟨(h2 i hi).1, ?_⟩⟩
    have := Nat.eq_of_beq_eq_true (h2 i hi).2
    simpa using this

end CFSG.Certificates.KB.Sound

end
