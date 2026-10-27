module

public import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Group
public import CFSG.Certificates.Kernel.J4.M24Rs
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.KM24.RS

open CFSG.KM24

theorem mAnd_iff (a b : Bool) : mAnd a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem mOr_iff (a b : Bool) : mOr a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem blt_iff (a b : ℕ) : Nat.blt a b = true ↔ a < b := by
  simp [Nat.blt_eq]

theorem ble_iff (a b : ℕ) : Nat.ble a b = true ↔ a ≤ b := by
  simp [Nat.ble_eq]

theorem beq_iff (a b : ℕ) : Nat.beq a b = true ↔ a = b := by
  simp [Nat.beq_eq]

theorem testBit_div_two' (x i : ℕ) : (x / 2).testBit i = x.testBit (i + 1) := by
  rw [Nat.testBit_succ]

theorem xor1_div (l : ℕ) : (l ^^^ 1) / 2 = l / 2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_div_two', testBit_div_two', Nat.testBit_xor]
  have : (1 : ℕ).testBit (i + 1) = false := by
    rw [Nat.testBit_succ]
    simp
  rw [this, Bool.xor_false]

theorem xor1_mod (l : ℕ) : (l ^^^ 1) % 2 = 1 - l % 2 := by
  have h0 : (l ^^^ 1).testBit 0 = !l.testBit 0 := by
    rw [Nat.testBit_xor]
    simp
  rw [Nat.testBit_zero, Nat.testBit_zero] at h0
  rcases Nat.mod_two_eq_zero_or_one l with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one (l ^^^ 1) with h' | h' <;> simp_all

theorem xor1_xor1 (l : ℕ) : l ^^^ 1 ^^^ 1 = l := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem xor1_lt {l k : ℕ} (hk : k % 2 = 0) (hl : l < k) : l ^^^ 1 < k := by
  have e1 := Nat.div_add_mod (l ^^^ 1) 2
  have e2 := Nat.div_add_mod l 2
  rw [xor1_div, xor1_mod] at e1
  have := Nat.mod_lt l (by norm_num : 0 < 2)
  omega

theorem xor1_lt_pow {l : ℕ} (hl : l < 2 ^ 16) : l ^^^ 1 < 2 ^ 16 :=
  xor1_lt (by norm_num) hl

variable {G : Type*} [Group G]

@[expose] def ltv (gen : ℕ → G) (l : ℕ) : G :=
  if l % 2 = 0 then gen (l / 2) else (gen (l / 2))⁻¹

theorem ltv_xor (gen : ℕ → G) (l : ℕ) : ltv gen (l ^^^ 1) = (ltv gen l)⁻¹ := by
  unfold ltv
  rw [xor1_div, xor1_mod]
  rcases Nat.mod_two_eq_zero_or_one l with h | h <;> simp [h]

theorem ltv_even (gen : ℕ → G) (g : ℕ) : ltv gen (2 * g) = gen g := by
  simp [ltv]

theorem ltv_odd (gen : ℕ → G) (g : ℕ) : ltv gen (2 * g + 1) = (gen g)⁻¹ := by
  have h1 : (2 * g + 1) % 2 = 1 := by omega
  have h2 : (2 * g + 1) / 2 = g := by omega
  simp [ltv, h1, h2]

@[expose] noncomputable def lv (gen : ℕ → G) (L : List ℕ) : G := (L.map (ltv gen)).prod

@[simp] theorem lv_nil (gen : ℕ → G) : lv gen [] = 1 := rfl

@[simp] theorem lv_cons (gen : ℕ → G) (c : ℕ) (L : List ℕ) :
    lv gen (c :: L) = ltv gen c * lv gen L := by
  simp [lv]

@[simp] theorem lv_append (gen : ℕ → G) (A B : List ℕ) : lv gen (A ++ B) = lv gen A * lv gen B := by
  simp [lv]

theorem lv_singleton (gen : ℕ → G) (c : ℕ) : lv gen [c] = ltv gen c := by simp

@[expose] def enc : List ℕ → ℕ
  | [] => 0
  | c :: L => c + 2 ^ 16 * enc L

@[expose] def Ok16 (L : List ℕ) : Prop := ∀ c ∈ L, c < 2 ^ 16

theorem lt_eq (w i : ℕ) : lt w i = w / 2 ^ (16 * i) % 2 ^ 16 := by
  change (w >>> (16 * i)) &&& 65535 = _
  rw [show (65535 : ℕ) = 2 ^ 16 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]

theorem lt_lt (w i : ℕ) : lt w i < 2 ^ 16 := by
  rw [lt_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem enc_lt {L : List ℕ} (h : Ok16 L) : enc L < 2 ^ (16 * L.length) := by
  induction L with
  | nil => simp [enc]
  | cons c L ih =>
    have hc := h c (List.mem_cons_self ..)
    have hL := ih fun d hd => h d (List.mem_cons_of_mem _ hd)
    simp only [enc, List.length_cons]
    rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (16 * L.length))]
    have : enc L + 1 ≤ 2 ^ (16 * L.length) := hL
    calc c + 2 ^ 16 * enc L < 2 ^ 16 * (enc L + 1) := by rw [Nat.mul_succ]; omega
      _ ≤ 2 ^ 16 * 2 ^ (16 * L.length) := Nat.mul_le_mul_left _ this

theorem enc_append (A B : List ℕ) : enc (A ++ B) = enc A + 2 ^ (16 * A.length) * enc B := by
  induction A with
  | nil => simp [enc]
  | cons c A ih =>
    simp only [List.cons_append, enc, ih, List.length_cons]
    rw [Nat.mul_succ, Nat.pow_add]
    ring

theorem ok16_append {A B : List ℕ} : Ok16 (A ++ B) ↔ Ok16 A ∧ Ok16 B := by
  simp [Ok16, or_imp, forall_and]

theorem lt_enc {L : List ℕ} (h : Ok16 L) (i : ℕ) : lt (enc L) i = L.getD i 0 := by
  induction L generalizing i with
  | nil => simp [enc, lt_eq]
  | cons c L ih =>
    have hc := h c (List.mem_cons_self ..)
    rw [lt_eq]
    cases i with
    | zero =>
      simp only [Nat.mul_zero, pow_zero, Nat.div_one, enc, List.getD_cons_zero]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
    | succ i =>
      have := ih (fun d hd => h d (List.mem_cons_of_mem _ hd)) i
      rw [lt_eq] at this
      simp only [enc, List.getD_cons_succ]
      have e : (c + 2 ^ 16 * enc L) / 2 ^ (16 * (i + 1)) = enc L / 2 ^ (16 * i) := by
        rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (16 * i)), ← Nat.div_div_eq_div_mul,
          Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hc, Nat.zero_add]
      rw [e, this]

@[expose] noncomputable def wl (w n : ℕ) : List ℕ := (List.range n).map (lt w)

@[simp] theorem wl_length (w n : ℕ) : (wl w n).length = n := by simp [wl]

theorem wl_ok (w n : ℕ) : Ok16 (wl w n) := by
  intro c hc
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
  exact lt_lt w i

theorem wl_succ (w n : ℕ) : wl w (n + 1) = wl w n ++ [lt w n] := by
  simp [wl, List.range_succ]

theorem getD_wl {w n i : ℕ} (hi : i < n) : (wl w n).getD i 0 = lt w i := by
  simp [wl, List.getD_eq_getElem?_getD, hi]

theorem wl_congr {w w' n : ℕ} (h : ∀ i < n, lt w i = lt w' i) : wl w n = wl w' n := by
  unfold wl
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.1 hi)

theorem wl_enc {L : List ℕ} (h : Ok16 L) : wl (enc L) L.length = L := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [wl, List.getElem_map, List.getElem_range]
    rw [lt_enc h]
    simp [List.getD_eq_getElem?_getD, h2]

theorem wl_enc' {L : List ℕ} (h : Ok16 L) {n : ℕ} (hn : n ≤ L.length) :
    wl (enc L) n = L.take n := by
  apply List.ext_getElem
  · simp [hn]
  · intro i h1 h2
    simp only [wl, List.getElem_map, List.getElem_range, List.getElem_take]
    rw [lt_enc h]
    simp only [wl_length] at h1
    simp [List.getD_eq_getElem?_getD, show i < L.length by omega]

theorem enc_wl {w n : ℕ} (hw : w < 2 ^ (16 * n)) : enc (wl w n) = w := by
  induction n generalizing w with
  | zero =>
    simp only [Nat.mul_zero, pow_zero, Nat.lt_one_iff] at hw
    subst hw
    simp [wl, enc]
  | succ n ih =>
    have e : wl w (n + 1) = lt w 0 :: wl (w / 2 ^ 16) n := by
      simp only [wl, List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      rw [Function.comp_apply, lt_eq, lt_eq, Nat.div_div_eq_div_mul, ← Nat.pow_add,
        show 16 * (i + 1) = 16 + 16 * i by ring]
    rw [e, enc, ih]
    · rw [lt_eq, Nat.mul_zero, pow_zero, Nat.div_one]
      exact Nat.mod_add_div w _
    · rw [Nat.div_lt_iff_lt_mul (by norm_num), ← Nat.pow_add]
      rw [Nat.mul_succ] at hw
      simpa [Nat.add_comm] using hw

theorem lor_eq (a b : ℕ) : Nat.lor a b = a ||| b := rfl

theorem or_shift {a k : ℕ} (ha : a < 2 ^ k) (b : ℕ) : a ||| (b <<< k) = a + 2 ^ k * b := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq]
  ring

theorem enc_concat {A B : List ℕ} (hA : Ok16 A) :
    Nat.lor (enc A) (Nat.shiftLeft (enc B) (Nat.mul 16 A.length)) = enc (A ++ B) := by
  change enc A ||| (enc B <<< (16 * A.length)) = _
  rw [or_shift (enc_lt hA), enc_append]

theorem push_eq {L : List ℕ} (hL : Ok16 L) (c : ℕ) :
    push (enc L) L.length c = (enc (L ++ [c]), (L ++ [c]).length) := by
  unfold push
  have e := enc_concat (B := [c]) hL
  simp only [enc, Nat.mul_zero, Nat.add_zero] at e
  rw [e]
  simp

theorem lmask_eq (k : ℕ) : lmask k = 2 ^ (16 * k) - 1 := by
  change (1 <<< (16 * k)) - 1 = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem land_lmask (w k : ℕ) : Nat.land w (lmask k) = w % 2 ^ (16 * k) := by
  rw [lmask_eq]
  exact Nat.and_two_pow_sub_one_eq_mod w _

theorem lt_land_lmask {w k i : ℕ} (hi : i < k) : lt (Nat.land w (lmask k)) i = lt w i := by
  rw [land_lmask, lt_eq, lt_eq, show 16 * k = 16 * i + 16 * (k - i) by omega, Nat.pow_add,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

theorem lt_shr (w k i : ℕ) : lt (Nat.shiftRight w (Nat.mul 16 k)) i = lt w (k + i) := by
  rw [lt_eq, lt_eq]
  change w >>> (16 * k) / 2 ^ (16 * i) % 2 ^ 16 = _
  rw [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_add]

theorem wl_land {w k n : ℕ} (h : n ≤ k) : wl (Nat.land w (lmask k)) n = wl w n :=
  wl_congr fun i hi => lt_land_lmask (by omega)

theorem wl_shr (w k n : ℕ) : wl (Nat.shiftRight w (Nat.mul 16 k)) n = (wl w (k + n)).drop k := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [wl, List.getElem_map, List.getElem_range, List.getElem_drop, lt_shr]

theorem wl_take {w n k : ℕ} (h : k ≤ n) : wl w k = (wl w n).take k := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp [wl]

theorem wl_drop (w n k : ℕ) : (wl w n).drop k = wl (Nat.shiftRight w (Nat.mul 16 k)) (n - k) := by
  rcases Nat.lt_or_ge n k with h | h
  · rw [List.drop_eq_nil_of_le (by simp; omega), show n - k = 0 by omega]
    simp [wl]
  · rw [wl_shr, Nat.add_sub_cancel' h]

theorem enc_mod {L : List ℕ} (h : Ok16 L) (k : ℕ) : enc L % 2 ^ (16 * k) = enc (L.take k) := by
  rcases Nat.lt_or_ge L.length k |>.symm with hk | hk
  · have ht : Ok16 (L.take k) := fun c hc => h c (List.mem_of_mem_take hc)
    have hl : (L.take k).length = k := by simp [hk]
    conv_lhs => rw [← List.take_append_drop k L, enc_append, hl]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
    have := enc_lt ht
    rwa [hl] at this
  · rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (enc_lt h) (Nat.pow_le_pow_right (by norm_num)
      (by omega))), List.take_of_length_le (by omega)]

theorem enc_cons_div {c : ℕ} (hc : c < 2 ^ 16) (L : List ℕ) : enc (c :: L) / 2 ^ 16 = enc L := by
  simp only [enc]
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hc, Nat.zero_add]

theorem enc_div {L : List ℕ} (h : Ok16 L) (k : ℕ) : enc L / 2 ^ (16 * k) = enc (L.drop k) := by
  induction k generalizing L with
  | zero => simp
  | succ k ih =>
    cases L with
    | nil => simp [enc]
    | cons c L =>
      rw [List.drop_succ_cons, ← ih (fun d hd => h d (List.mem_cons_of_mem _ hd)), Nat.mul_succ,
        Nat.pow_add, Nat.mul_comm (2 ^ (16 * k)), ← Nat.div_div_eq_div_mul,
        enc_cons_div (h c (List.mem_cons_self ..))]

theorem enc_shr {L : List ℕ} (h : Ok16 L) (k : ℕ) :
    Nat.shiftRight (enc L) (Nat.mul 16 k) = enc (L.drop k) := by
  change enc L >>> (16 * k) = _
  rw [Nat.shiftRight_eq_div_pow, enc_div h]

theorem enc_shr1 {L : List ℕ} (h : Ok16 L) : Nat.shiftRight (enc L) 16 = enc (L.drop 1) := by
  have := enc_shr h 1
  exact this

theorem ok16_drop {L : List ℕ} (h : Ok16 L) (k : ℕ) : Ok16 (L.drop k) :=
  fun c hc => h c (List.mem_of_mem_drop hc)

theorem ok16_take {L : List ℕ} (h : Ok16 L) (k : ℕ) : Ok16 (L.take k) :=
  fun c hc => h c (List.mem_of_mem_take hc)

theorem enc_land {L : List ℕ} (h : Ok16 L) (k : ℕ) : Nat.land (enc L) (lmask k) = enc (L.take k) := by
  rw [land_lmask, enc_mod h]

theorem pk_eq {a m : ℕ} (hm : m < 2 ^ 16) : pk a m = m + 2 ^ 16 * a := by
  unfold pk
  change m ||| (a <<< 16) = _
  rw [or_shift hm]

theorem pn_pk {a m : ℕ} (hm : m < 2 ^ 16) : pn (pk a m) = m := by
  rw [pk_eq hm]
  change (m + 2 ^ 16 * a) &&& 65535 = _
  rw [show (65535 : ℕ) = 2 ^ 16 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hm]

theorem pw_pk {a m : ℕ} (hm : m < 2 ^ 16) : pw (pk a m) = a := by
  rw [pk_eq hm]
  change (m + 2 ^ 16 * a) >>> 16 = _
  rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hm,
    Nat.zero_add]

theorem pn_lt (x : ℕ) : pn x < 2 ^ 16 := by
  change x &&& 65535 < _
  exact Nat.and_lt_two_pow _ (by norm_num)

theorem getD_of_lt {L : List ℕ} {i d : ℕ} (h : i < L.length) : L.getD i d = L[i] := by
  simp [List.getD_eq_getElem?_getD, h]

@[expose] noncomputable def frStep (acc : List ℕ) (c : ℕ) : List ℕ :=
  if 0 < acc.length ∧ acc.getD (acc.length - 1) 0 = c ^^^ 1 then acc.dropLast else acc ++ [c]

@[expose] noncomputable def frL (L : List ℕ) : List ℕ := L.foldl frStep []

theorem frL_concat (L : List ℕ) (c : ℕ) : frL (L ++ [c]) = frStep (frL L) c := by
  simp [frL, List.foldl_append]

theorem mem_frStep {acc : List ℕ} {c d : ℕ} (h : d ∈ frStep acc c) : d ∈ acc ∨ d = c := by
  unfold frStep at h
  split at h
  · exact Or.inl (List.mem_of_mem_dropLast h)
  · simpa using h

theorem mem_frL {L : List ℕ} {d : ℕ} (h : d ∈ frL L) : d ∈ L := by
  induction L using List.reverseRecOn with
  | nil => simp [frL] at h
  | append_singleton L c ih =>
    rw [frL_concat] at h
    rcases mem_frStep h with h | h
    · exact List.mem_append_left _ (ih h)
    · simp [h]

theorem length_frL (L : List ℕ) : (frL L).length ≤ L.length := by
  induction L using List.reverseRecOn with
  | nil => simp [frL]
  | append_singleton L c ih =>
    rw [frL_concat]
    unfold frStep
    split
    · simp only [List.length_dropLast, List.length_append, List.length_singleton]
      omega
    · simp only [List.length_append, List.length_singleton]
      omega

theorem ok16_frL {L : List ℕ} (h : Ok16 L) : Ok16 (frL L) := fun c hc => h c (mem_frL hc)

theorem lv_frL (gen : ℕ → G) (L : List ℕ) : lv gen (frL L) = lv gen L := by
  induction L using List.reverseRecOn with
  | nil => simp [frL]
  | append_singleton L c ih =>
    rw [frL_concat, lv_append, ← ih]
    unfold frStep
    split
    · rename_i hc
      obtain ⟨h0, h1⟩ := hc
      have e : frL L = (frL L).dropLast ++ [c ^^^ 1] := by
        conv_lhs => rw [← List.dropLast_append_getLast (List.ne_nil_of_length_pos h0)]
        congr 2
        rw [List.getLast_eq_getElem, ← h1, getD_of_lt (by omega)]
      conv_rhs => rw [e]
      simp [ltv_xor]
    · simp

@[expose] noncomputable def frBody (w i : ℕ) (acc : ℕ × ℕ) : ℕ × ℕ :=
  Prod.rec (motive := fun _ => Nat × Nat) (fun a m =>
    Bool.rec (push a m (lt w i))
      (Prod.mk (Nat.land a (lmask (Nat.sub m (nat_lit 1)))) (Nat.sub m (nat_lit 1)))
      (mAnd (Nat.blt (nat_lit 0) m)
        (Nat.beq (lt a (Nat.sub m (nat_lit 1))) (Nat.xor (lt w i) (nat_lit 1))))) acc

theorem freeRed_succ (w n : ℕ) : freeRed w (n + 1) = frBody w n (freeRed w n) := rfl

theorem freeRed_eq (w n : ℕ) : freeRed w n = (enc (frL (wl w n)), (frL (wl w n)).length) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hok : Ok16 (frL (wl w n)) := ok16_frL (wl_ok w n)
    rw [freeRed_succ, ih, wl_succ, frL_concat]
    unfold frBody
    dsimp only
    unfold frStep
    by_cases hc : 0 < (frL (wl w n)).length ∧
        (frL (wl w n)).getD ((frL (wl w n)).length - 1) 0 = lt w n ^^^ 1
    · rw [ite_eq_left hc]
      have hb : mAnd (Nat.blt 0 (frL (wl w n)).length)
          (Nat.beq (lt (enc (frL (wl w n))) (Nat.sub (frL (wl w n)).length 1)) (Nat.xor (lt w n) 1)) =
          true := by
        rw [mAnd_iff, blt_iff, beq_iff, lt_enc hok]
        exact hc
      rw [hb]
      dsimp only
      rw [enc_land hok, List.dropLast_eq_take]
      simp only [Nat.sub_eq, List.length_take]
      congr 1
      omega
    · rw [ite_eq_right hc]
      have hb : mAnd (Nat.blt 0 (frL (wl w n)).length)
          (Nat.beq (lt (enc (frL (wl w n))) (Nat.sub (frL (wl w n)).length 1)) (Nat.xor (lt w n) 1)) =
          false := by
        rw [← Bool.not_eq_true, mAnd_iff, blt_iff, beq_iff, lt_enc hok]
        exact hc
      rw [hb]
      exact push_eq hok _

@[expose] noncomputable def cyStep (L : List ℕ) : List ℕ :=
  if 1 < L.length ∧ L.getD 0 0 = L.getD (L.length - 1) 0 ^^^ 1 then (L.drop 1).take (L.length - 2)
  else L

theorem cyStep_decomp {L : List ℕ} (h : 1 < L.length) :
    L = L.getD 0 0 :: ((L.drop 1).take (L.length - 2) ++ [L.getD (L.length - 1) 0]) := by
  apply List.ext_getElem
  · simp
    omega
  · intro i h1 h2
    rcases i with _ | i
    · simp [List.getD_eq_getElem?_getD, show 0 < L.length by omega]
    · simp only [List.getElem_cons_succ]
      by_cases hi : i < L.length - 2
      · rw [List.getElem_append_left (by simp; omega)]
        simp
      · rw [List.getElem_append_right (by simp; omega)]
        simp only [List.length_take, List.length_drop, List.getElem_singleton]
        rw [getD_of_lt (by omega)]
        congr 1
        omega

theorem mem_cyStep {L : List ℕ} {d : ℕ} (h : d ∈ cyStep L) : d ∈ L := by
  unfold cyStep at h
  split at h
  · exact List.mem_of_mem_drop (List.mem_of_mem_take h)
  · exact h

theorem length_cyStep (L : List ℕ) : (cyStep L).length ≤ L.length := by
  unfold cyStep
  split
  · simp
  · exact le_refl _

theorem lv_cyStep (gen : ℕ → G) {L : List ℕ} (h : lv gen L = 1) : lv gen (cyStep L) = 1 := by
  unfold cyStep
  split
  · rename_i hc
    obtain ⟨h0, h1⟩ := hc
    rw [cyStep_decomp h0, h1, lv_cons, lv_append, lv_singleton, ltv_xor] at h
    have := congrArg (fun z => ltv gen (L.getD (L.length - 1) 0) * z *
      (ltv gen (L.getD (L.length - 1) 0))⁻¹) h
    simp only [mul_one, mul_inv_cancel] at this
    rw [← this]
    group
  · exact h

theorem natRec_iter {α : Type*} (f : α → α) (x : α) (k : ℕ) :
    Nat.rec (motive := fun _ => α) x (fun _ acc => f acc) k = f^[k] x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ih]

@[expose] noncomputable def cyL (L : List ℕ) : List ℕ := cyStep^[L.length / 2] L

theorem mem_cyL {L : List ℕ} {d : ℕ} (h : d ∈ cyL L) : d ∈ L := by
  unfold cyL at h
  generalize L.length / 2 = k at h
  induction k generalizing L with
  | zero => exact h
  | succ k ih =>
    rw [Function.iterate_succ_apply] at h
    exact mem_cyStep (ih h)

theorem length_cyL (L : List ℕ) : (cyL L).length ≤ L.length := by
  unfold cyL
  generalize L.length / 2 = k
  induction k generalizing L with
  | zero => exact le_refl _
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact (ih _).trans (length_cyStep L)

theorem lv_cyL (gen : ℕ → G) {L : List ℕ} (h : lv gen L = 1) : lv gen (cyL L) = 1 := by
  unfold cyL
  generalize L.length / 2 = k
  induction k generalizing L with
  | zero => exact h
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact ih (lv_cyStep gen h)

theorem ok16_cyL {L : List ℕ} (h : Ok16 L) : Ok16 (cyL L) := fun c hc => h c (mem_cyL hc)

@[expose] noncomputable def cyBody (acc : ℕ × ℕ) : ℕ × ℕ :=
  Prod.rec (motive := fun _ => ℕ × ℕ) (fun w n =>
    Bool.rec (Prod.mk w n)
      (Prod.mk (Nat.land (Nat.shiftRight w (nat_lit 16)) (lmask (Nat.sub n (nat_lit 2))))
        (Nat.sub n (nat_lit 2)))
      (mAnd (Nat.blt (nat_lit 1) n)
        (Nat.beq (lt w (nat_lit 0)) (Nat.xor (lt w (Nat.sub n (nat_lit 1))) (nat_lit 1))))) acc

theorem cyBody_eq {L : List ℕ} (h : Ok16 L) : cyBody (enc L, L.length) =
    (enc (cyStep L), (cyStep L).length) := by
  unfold cyBody cyStep
  dsimp only
  by_cases hc : 1 < L.length ∧ L.getD 0 0 = L.getD (L.length - 1) 0 ^^^ 1
  · rw [ite_eq_left hc]
    have hb : mAnd (Nat.blt 1 L.length) (Nat.beq (lt (enc L) 0) (Nat.xor (lt (enc L) (Nat.sub L.length 1)) 1))
        = true := by
      rw [mAnd_iff, blt_iff, beq_iff, lt_enc h, lt_enc h]
      exact hc
    rw [hb]
    dsimp only
    rw [enc_shr1 h, enc_land (ok16_drop h 1)]
    simp
    omega
  · rw [ite_eq_right hc]
    have hb : mAnd (Nat.blt 1 L.length) (Nat.beq (lt (enc L) 0) (Nat.xor (lt (enc L) (Nat.sub L.length 1)) 1))
        = false := by
      rw [← Bool.not_eq_true, mAnd_iff, blt_iff, beq_iff, lt_enc h, lt_enc h]
      exact hc
    rw [hb]

theorem ok16_cyStep {L : List ℕ} (h : Ok16 L) : Ok16 (cyStep L) := fun c hc => h c (mem_cyStep hc)

theorem cyIter_eq {L : List ℕ} (h : Ok16 L) (k : ℕ) :
    cyBody^[k] (enc L, L.length) = (enc (cyStep^[k] L), (cyStep^[k] L).length) := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, cyBody_eq h]
    exact ih (ok16_cyStep h)

theorem pk_eq_pk (a m : ℕ) : Prod.rec (motive := fun _ => ℕ) pk (a, m) = pk a m := rfl

theorem cycRed_eq {L : List ℕ} (h : Ok16 L) :
    cycRed (enc L, L.length) = pk (enc (cyL L)) (cyL L).length := by
  have e : cycRed (enc L, L.length) = Prod.rec (motive := fun _ => ℕ) pk
      (cyBody^[L.length / 2] (enc L, L.length)) := by
    rw [← natRec_iter]
    rfl
  rw [e, cyIter_eq h]
  rfl

@[expose] noncomputable def redL (L : List ℕ) : List ℕ := cyL (frL L)

theorem red_eq (w n : ℕ) : red w n = pk (enc (redL (wl w n))) (redL (wl w n)).length := by
  unfold red
  rw [freeRed_eq, cycRed_eq (ok16_frL (wl_ok w n))]
  rfl

theorem red_eq_enc {L : List ℕ} (h : Ok16 L) :
    red (enc L) L.length = pk (enc (redL L)) (redL L).length := by
  rw [red_eq, wl_enc h]

theorem mem_redL {L : List ℕ} {d : ℕ} (h : d ∈ redL L) : d ∈ L := mem_frL (mem_cyL h)

theorem length_redL (L : List ℕ) : (redL L).length ≤ L.length :=
  (length_cyL _).trans (length_frL L)

theorem ok16_redL {L : List ℕ} (h : Ok16 L) : Ok16 (redL L) := fun c hc => h c (mem_redL hc)

theorem lv_redL (gen : ℕ → G) {L : List ℕ} (h : lv gen L = 1) : lv gen (redL L) = 1 := by
  unfold redL
  exact lv_cyL gen (by rw [lv_frL]; exact h)

@[expose] noncomputable def invL (L : List ℕ) : List ℕ := (L.map (· ^^^ 1)).reverse

@[simp] theorem length_invL (L : List ℕ) : (invL L).length = L.length := by simp [invL]

theorem invL_concat (L : List ℕ) (c : ℕ) : invL (L ++ [c]) = (c ^^^ 1) :: invL L := by
  simp [invL]

theorem invL_append (A B : List ℕ) : invL (A ++ B) = invL B ++ invL A := by
  simp [invL]

theorem mem_invL {L : List ℕ} {d : ℕ} (h : d ∈ invL L) : ∃ c ∈ L, d = c ^^^ 1 := by
  simp only [invL, List.mem_reverse, List.mem_map] at h
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨c, hc, rfl⟩

theorem ok16_invL {L : List ℕ} (h : Ok16 L) : Ok16 (invL L) := by
  intro d hd
  obtain ⟨c, hc, rfl⟩ := mem_invL hd
  exact xor1_lt_pow (h c hc)

theorem lv_invL (gen : ℕ → G) (L : List ℕ) : lv gen (invL L) = (lv gen L)⁻¹ := by
  induction L using List.reverseRecOn with
  | nil => simp [invL]
  | append_singleton L c ih => rw [invL_concat, lv_cons, ih, ltv_xor, lv_append, lv_singleton, mul_inv_rev]

theorem natRec_succ {α : Sort*} (x : α) (f : ℕ → α → α) (k : ℕ) :
    Nat.rec (motive := fun _ => α) x f (k + 1) = f k (Nat.rec (motive := fun _ => α) x f k) := rfl

@[expose] noncomputable def wiRec (w n k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (Nat.xor (lt w i) (nat_lit 1))
      (Nat.mul (nat_lit 16) (Nat.sub (Nat.sub n i) (nat_lit 1))))) k

theorem wiRec_succ (w n k : ℕ) : wiRec w n (k + 1) = Nat.lor (wiRec w n k)
    (Nat.shiftLeft (Nat.xor (lt w k) 1) (Nat.mul 16 (Nat.sub (Nat.sub n k) 1))) := rfl

theorem wInv_aux (w n : ℕ) : ∀ k ≤ n, wiRec w n k = 2 ^ (16 * (n - k)) * enc (invL (wl w k)) := by
  intro k hk
  induction k with
  | zero => simp [invL, wl, enc, wiRec]
  | succ k ih =>
    rw [wiRec_succ, ih (by omega), wl_succ, invL_concat]
    change 2 ^ (16 * (n - k)) * enc (invL (wl w k)) ||| ((lt w k ^^^ 1) <<< (16 * (n - k - 1))) = _
    have e1 : 2 ^ (16 * (n - k)) * enc (invL (wl w k)) =
        (enc (invL (wl w k)) <<< 16) <<< (16 * (n - k - 1)) := by
      rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.mul_assoc, ← Nat.pow_add,
        show 16 + 16 * (n - k - 1) = 16 * (n - k) by omega, Nat.mul_comm]
    rw [e1, ← Nat.shiftLeft_or_distrib, Nat.or_comm, or_shift (xor1_lt_pow (lt_lt w k)),
      Nat.shiftLeft_eq, show n - (k + 1) = n - k - 1 by omega]
    simp only [enc]
    ring

theorem wInv_eq (w n : ℕ) : wInv w n = enc (invL (wl w n)) := by
  have := wInv_aux w n n (le_refl n)
  rw [Nat.sub_self, Nat.mul_zero, pow_zero, Nat.one_mul] at this
  exact this

theorem rot_eq {L : List ℕ} (h : Ok16 L) (a : ℕ) :
    rot (enc L) L.length a = enc (L.drop a ++ L.take a) := by
  unfold rot
  rw [enc_shr h, enc_land h]
  have e := enc_concat (B := L.take a) (ok16_drop h a)
  rw [List.length_drop] at e
  exact e

theorem lv_rot (gen : ℕ → G) {L : List ℕ} (h : lv gen L = 1) (a : ℕ) :
    lv gen (L.drop a ++ L.take a) = 1 := by
  rw [← List.take_append_drop a L, lv_append] at h
  rw [lv_append]
  have : lv gen (L.drop a) = (lv gen (L.take a))⁻¹ := eq_inv_of_mul_eq_one_right h
  rw [this, inv_mul_cancel]

theorem length_rot (L : List ℕ) (a : ℕ) : (L.drop a ++ L.take a).length = L.length := by
  simp only [List.length_append, List.length_drop, List.length_take]
  omega

theorem mem_rot {L : List ℕ} {a d : ℕ} (h : d ∈ L.drop a ++ L.take a) : d ∈ L := by
  rcases List.mem_append.1 h with h | h
  · exact List.mem_of_mem_drop h
  · exact List.mem_of_mem_take h

@[expose] noncomputable def solL (L : List ℕ) (p : ℕ) : List ℕ :=
  frL (invL (L.take p) ++ invL (L.drop (p + 1)))

theorem solveAt_eq (w n p : ℕ) (hp : p < n) :
    solveAt w n p = if lt w p % 2 = 1 then (enc (invL (solL (wl w n) p)), (solL (wl w n) p).length)
      else (enc (solL (wl w n) p), (solL (wl w n) p).length) := by
  unfold solveAt
  have hA : Ok16 (invL (wl w p)) := ok16_invL (wl_ok w p)
  rw [wInv_eq, wInv_eq, wl_land (le_refl p)]
  have e := enc_concat (B := invL (wl (Nat.shiftRight w (Nat.mul 16 (Nat.succ p))) (n - p - 1))) hA
  rw [length_invL, wl_length] at e
  simp only [Nat.sub_eq]
  rw [e, freeRed_eq]
  have hl : (invL (wl w p) ++ invL (wl (Nat.shiftRight w (Nat.mul 16 (Nat.succ p))) (n - p - 1))).length
      = n - 1 := by simp; omega
  rw [← hl, wl_enc (ok16_append.2 ⟨hA, ok16_invL (wl_ok _ _)⟩)]
  have h1 : wl w p = (wl w n).take p := wl_take (by omega)
  have h2 : wl (Nat.shiftRight w (Nat.mul 16 (Nat.succ p))) (n - p - 1) = (wl w n).drop (p + 1) := by
    rw [wl_drop]
    rfl
  rw [h1, h2]
  dsimp only
  have hb : Nat.beq (Nat.land (lt w p) 1) 1 = decide (lt w p % 2 = 1) := by
    change Nat.beq (lt w p &&& 1) 1 = _
    rw [Nat.and_one_is_mod, Bool.eq_iff_iff, beq_iff, decide_eq_true_iff]
  rw [hb]
  unfold solL
  by_cases hpar : lt w p % 2 = 1
  · simp only [hpar, decide_true, ite_true]
    rw [wInv_eq, wl_enc (ok16_frL (ok16_append.2 ⟨ok16_invL (ok16_take (wl_ok _ _) _),
      ok16_invL (ok16_drop (wl_ok _ _) _)⟩))]
  · simp only [hpar, decide_false, ite_false]

@[expose] noncomputable def subL (L : List ℕ) (g : ℕ) (S Si : List ℕ) : List ℕ :=
  L.flatMap fun l => if l / 2 = g then (if l % 2 = 1 then Si else S) else [l]

theorem subL_concat (L : List ℕ) (c g : ℕ) (S Si : List ℕ) :
    subL (L ++ [c]) g S Si = subL L g S Si ++ (if c / 2 = g then (if c % 2 = 1 then Si else S) else [c]) := by
  simp [subL]

@[expose] noncomputable def sbBody (w g s si ns i : ℕ) (acc : ℕ × ℕ) : ℕ × ℕ :=
  Prod.rec (motive := fun _ => Nat × Nat) (fun a m =>
    Bool.rec (push a m (lt w i))
      (Prod.mk (Nat.lor a (Nat.shiftLeft
          (Bool.rec s si (Nat.beq (Nat.land (lt w i) (nat_lit 1)) (nat_lit 1)))
          (Nat.mul (nat_lit 16) m))) (Nat.add m ns))
      (Nat.beq (Nat.shiftRight (lt w i) (nat_lit 1)) g)) acc

@[expose] noncomputable def sbRec (w g s si ns k : ℕ) : ℕ × ℕ :=
  Nat.rec (motive := fun _ => Nat × Nat) (Prod.mk (nat_lit 0) (nat_lit 0))
    (fun i acc => sbBody w g s si ns i acc) k

theorem subst_eq_rec (w n g s si ns : ℕ) :
    subst w n g s si ns = Prod.rec (motive := fun _ => ℕ) red (sbRec w g s si ns n) := rfl

theorem shr1_eq (x : ℕ) : Nat.shiftRight x 1 = x / 2 := by
  change x >>> 1 = _
  rw [Nat.shiftRight_eq_div_pow, pow_one]

theorem beq_land1 (x : ℕ) : Nat.beq (Nat.land x 1) 1 = decide (x % 2 = 1) := by
  change Nat.beq (x &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Bool.eq_iff_iff, beq_iff, decide_eq_true_iff]

theorem beq_decide (a b : ℕ) : Nat.beq a b = decide (a = b) := by
  rw [Bool.eq_iff_iff, beq_iff, decide_eq_true_iff]

theorem sbRec_eq {w g : ℕ} {S Si : List ℕ} (hS : Ok16 S) (hSi : Ok16 Si) (hl : Si.length = S.length)
    (k : ℕ) : sbRec w g (enc S) (enc Si) S.length k =
      (enc (subL (wl w k) g S Si), (subL (wl w k) g S Si).length) := by
  have hok : ∀ k, Ok16 (subL (wl w k) g S Si) := by
    intro k d hd
    simp only [subL, List.mem_flatMap] at hd
    obtain ⟨l, hl', hd⟩ := hd
    split at hd
    · split at hd
      · exact hSi d hd
      · exact hS d hd
    · rw [List.mem_singleton] at hd
      rw [hd]
      exact wl_ok w k l hl'
  induction k with
  | zero => rfl
  | succ k ih =>
    change sbBody w g (enc S) (enc Si) S.length k (sbRec w g (enc S) (enc Si) S.length k) = _
    rw [ih, wl_succ, subL_concat]
    unfold sbBody
    dsimp only
    rw [shr1_eq, beq_land1, beq_decide]
    by_cases h1 : lt w k / 2 = g
    · simp only [h1, decide_true, ite_true]
      by_cases h2 : lt w k % 2 = 1
      · simp only [h2, decide_true, ite_true]
        rw [enc_concat (hok k)]
        simp [hl]
      · simp only [h2, decide_false, ite_false]
        rw [enc_concat (hok k)]
        simp
    · simp only [h1, decide_false, ite_false]
      exact push_eq (hok k) _

theorem subst_eq {w n g : ℕ} {S Si : List ℕ} (hS : Ok16 S) (hSi : Ok16 Si)
    (hl : Si.length = S.length) :
    subst w n g (enc S) (enc Si) S.length =
      pk (enc (redL (subL (wl w n) g S Si))) (redL (subL (wl w n) g S Si)).length := by
  rw [subst_eq_rec, sbRec_eq hS hSi hl]
  dsimp only
  rw [red_eq_enc]
  intro d hd
  simp only [subL, List.mem_flatMap] at hd
  obtain ⟨l, hl', hd⟩ := hd
  split at hd
  · split at hd
    · exact hSi d hd
    · exact hS d hd
  · rw [List.mem_singleton] at hd
    rw [hd]
    exact wl_ok w n l hl'

theorem lv_subL (gen : ℕ → G) (L : List ℕ) (g : ℕ) {S Si : List ℕ} (hS : lv gen S = gen g)
    (hSi : lv gen Si = (gen g)⁻¹) : lv gen (subL L g S Si) = lv gen L := by
  induction L with
  | nil => simp [subL]
  | cons l L ih =>
    have e : subL (l :: L) g S Si = (if l / 2 = g then (if l % 2 = 1 then Si else S) else [l]) ++
        subL L g S Si := by simp [subL]
    rw [e, lv_append, ih, lv_cons]
    congr 1
    split
    · rename_i h1
      split
      · rename_i h2
        rw [hSi]
        unfold ltv
        rw [ite_eq_right (by omega), h1]
      · rename_i h2
        rw [hS]
        unfold ltv
        rw [ite_eq_left (by omega), h1]
    · simp

theorem mem_subL {L : List ℕ} {g : ℕ} {S Si : List ℕ} {d : ℕ} (h : d ∈ subL L g S Si) :
    (d ∈ L ∧ d / 2 ≠ g) ∨ d ∈ S ∨ d ∈ Si := by
  simp only [subL, List.mem_flatMap] at h
  obtain ⟨l, hl, hd⟩ := h
  split at hd
  · split at hd
    · exact Or.inr (Or.inr hd)
    · exact Or.inr (Or.inl hd)
  · rename_i h1
    rw [List.mem_singleton] at hd
    subst hd
    exact Or.inl ⟨hl, h1⟩

@[expose] noncomputable def ocRec (w g k : ℕ) : ℕ × ℕ :=
  Nat.rec (motive := fun _ => Nat × Nat) (Prod.mk (nat_lit 0) (nat_lit 0))
    (fun i acc => Prod.rec (motive := fun _ => Nat × Nat) (fun c p =>
      Bool.rec (Prod.mk c p) (Prod.mk (Nat.succ c) i)
        (Nat.beq (Nat.shiftRight (lt w i) (nat_lit 1)) g)) acc) k

theorem occ_eq (w n g : ℕ) : occ w n g = ocRec w g n := rfl

theorem ocRec_succ (w g k : ℕ) : ocRec w g (k + 1) =
    Prod.rec (motive := fun _ => Nat × Nat) (fun c p =>
      Bool.rec (Prod.mk c p) (Prod.mk (Nat.succ c) k)
        (Nat.beq (Nat.shiftRight (lt w k) (nat_lit 1)) g)) (ocRec w g k) := rfl

theorem ocRec_inv (w g : ℕ) : ∀ k, (ocRec w g k).1 =
      ((Finset.range k).filter fun i => lt w i / 2 = g).card ∧
      (0 < (ocRec w g k).1 → (ocRec w g k).2 < k ∧ lt w (ocRec w g k).2 / 2 = g) := by
  intro k
  induction k with
  | zero => simp [ocRec]
  | succ k ih =>
    rw [ocRec_succ]
    generalize ocRec w g k = q at ih ⊢
    obtain ⟨c, p⟩ := q
    simp only at ih ⊢
    rw [shr1_eq, beq_decide, Finset.range_add_one, Finset.filter_insert]
    by_cases h : lt w k / 2 = g
    · simp only [h, decide_true, ite_true]
      rw [Finset.card_insert_of_notMem (by simp)]
      exact ⟨by rw [ih.1], fun _ => ⟨by omega, trivial⟩⟩
    · simp only [h, decide_false, ite_false]
      exact ⟨ih.1, fun hc => ⟨by have := (ih.2 hc).1; omega, (ih.2 hc).2⟩⟩

theorem occ_spec {w n g : ℕ} (h : (occ w n g).1 = 1) :
    (occ w n g).2 < n ∧ lt w (occ w n g).2 / 2 = g ∧
      ∀ i < n, lt w i / 2 = g → i = (occ w n g).2 := by
  rw [occ_eq] at h ⊢
  obtain ⟨hc, hp⟩ := ocRec_inv w g n
  obtain ⟨hp1, hp2⟩ := hp (by omega)
  refine ⟨hp1, hp2, fun i hi hig => ?_⟩
  rw [h] at hc
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hc.symm
  have h1 : i ∈ (Finset.range n).filter fun i => lt w i / 2 = g := by simp [hi, hig]
  have h2 : (ocRec w g n).2 ∈ (Finset.range n).filter fun i => lt w i / 2 = g := by simp [hp1, hp2]
  rw [ha, Finset.mem_singleton] at h1 h2
  rw [h1, h2]

theorem getR_eq (L : List ℕ) (i : ℕ) : getR L i = L.getD i 0 := by
  induction L generalizing i with
  | nil => rfl
  | cons h t ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem setR_eq (L : List ℕ) (i x : ℕ) : setR L i x = L.set i x := by
  induction L generalizing i with
  | nil => rfl
  | cons h t ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change List.cons h (setR t i x) = _
      rw [ih]
      rfl

theorem mapSubst_eq (L : List ℕ) (g s si ns : ℕ) :
    mapSubst L g s si ns = L.map fun h => subst (pw h) (pn h) g s si ns := by
  induction L with
  | nil => rfl
  | cons h t ih =>
    change List.cons _ (mapSubst t g s si ns) = _
    rw [ih]
    rfl

theorem appR_eq (A B : List ℕ) : appR A B = A ++ B := by
  induction A with
  | nil => rfl
  | cons h t ih =>
    change List.cons h (appR t B) = _
    rw [ih]
    rfl

theorem eqRL_eq {A B : List ℕ} (h : eqRL A B = true) : A = B := by
  induction A generalizing B with
  | nil =>
    cases B with
    | nil => rfl
    | cons _ _ =>
      change false = true at h
      exact absurd h (by decide)
  | cons a t ih =>
    cases B with
    | nil =>
      change false = true at h
      exact absurd h (by decide)
    | cons b u =>
      change mAnd (Nat.beq a b) (eqRL t u) = true at h
      rw [mAnd_iff, beq_iff] at h
      rw [h.1, ih h.2]

theorem mem_getD {L : List ℕ} {i : ℕ} (h : i < L.length) : L.getD i 0 ∈ L := by
  rw [getD_of_lt h]
  exact List.getElem_mem h

theorem mem_set {L : List ℕ} {i x d : ℕ} (h : d ∈ L.set i x) : d ∈ L ∨ d = x := by
  rcases List.mem_or_eq_of_mem_set h with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem live_iff (G g : ℕ) : live G g = true ↔ G.testBit g = true := by
  unfold live
  rw [blt_iff]
  change 0 < G &&& (1 <<< g) ↔ _
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  constructor
  · intro h
    by_contra hb
    have : G &&& 2 ^ g = 0 := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_and, Nat.zero_testBit]
      by_cases hj : g = j
      · subst hj
        rw [Bool.eq_false_iff.2 hb, Bool.false_and]
      · rw [Nat.testBit_two_pow_of_ne hj, Bool.and_false]
    omega
  · intro h
    apply Nat.pos_of_ne_zero
    intro h0
    have h1 : (G &&& 2 ^ g).testBit g = true := by
      rw [Nat.testBit_and, h, Nat.testBit_two_pow_self]
      rfl
    rw [h0, Nat.zero_testBit] at h1
    exact absurd h1 (by decide)

theorem testBit_sub_pow {G g : ℕ} (h : G.testBit g = true) (j : ℕ) :
    (G - 2 ^ g).testBit j = (G.testBit j && !decide (j = g)) := by
  have hq : (G / 2 ^ g) % 2 = 1 := by
    have := Nat.testBit_div_two_pow (n := g) G 0
    rw [Nat.zero_add, h, Nat.testBit_zero] at this
    simpa using this
  have hr : G % 2 ^ g < 2 ^ g := Nat.mod_lt _ (by positivity)
  have e1 : G = 2 ^ g * (G / 2 ^ g) + G % 2 ^ g := (Nat.div_add_mod G _).symm
  have hx : 1 ≤ G / 2 ^ g := Nat.pos_of_ne_zero fun h0 => by rw [h0] at hq; simp at hq
  have e2 : G - 2 ^ g = 2 ^ g * (G / 2 ^ g - 1) + G % 2 ^ g := by
    rw [Nat.mul_sub_one]
    have : 2 ^ g ≤ 2 ^ g * (G / 2 ^ g) := Nat.le_mul_of_pos_right _ hx
    omega
  rw [e2, Nat.testBit_two_pow_mul_add _ hr]
  conv_rhs => rw [e1, Nat.testBit_two_pow_mul_add _ hr]
  by_cases hj : j < g
  · simp [hj, show j ≠ g by omega]
  · simp only [hj, ite_false]
    by_cases hjg : j = g
    · subst hjg
      simp only [Nat.sub_self, Nat.testBit_zero, decide_true, Bool.not_true, Bool.and_false]
      have : (G / 2 ^ j - 1) % 2 = 0 := by omega
      simp [this]
    · simp only [hjg, decide_false, Bool.not_false, Bool.and_true]
      obtain ⟨k, hk⟩ : ∃ k, j - g = k + 1 := ⟨j - g - 1, by omega⟩
      rw [hk, ← Nat.testBit_div_two, ← Nat.testBit_div_two]
      congr 1
      omega

theorem t8_eq (T i : ℕ) : t8 T i = T / 2 ^ (8 * i) % 256 := by
  change (T >>> (8 * i)) &&& 255 = _
  rw [show (255 : ℕ) = 2 ^ 8 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]

theorem natRec_and_iff {f : ℕ → Bool} : ∀ k, Nat.rec (motive := fun _ => Bool) true
    (fun i acc => mAnd acc (f i)) k = true ↔ ∀ i < k, f i = true := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    change mAnd (Nat.rec (motive := fun _ => Bool) true (fun i acc => mAnd acc (f i)) k) (f k) = true
      ↔ _
    rw [mAnd_iff, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · exact h1 i hi
      · rw [hi]
        exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h k (by omega)⟩

theorem chkTable_spec {T P k2 nc : ℕ} (h : chkTable T P k2 nc = true) :
    (∀ i < nc * k2, t8 T i < nc) ∧
      ∀ d, 0 < d → d < nc → t8 P (2 * d) < d ∧ t8 P (2 * d + 1) < k2 ∧
        t8 T (t8 P (2 * d) * k2 + t8 P (2 * d + 1)) = d := by
  unfold chkTable at h
  rw [mAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  rw [natRec_and_iff] at h1 h2
  refine ⟨fun i hi => (blt_iff _ _).1 (h1 i hi), fun d hd0 hd => ?_⟩
  have := h2 (d - 1) (by change d - 1 < nc - 1; omega)
  rw [mAnd_iff, mAnd_iff, blt_iff, blt_iff, beq_iff] at this
  have e : Nat.succ (d - 1) = d := by omega
  simp only [e] at this
  exact ⟨this.1, this.2.1, this.2.2⟩

@[expose] noncomputable def gnRec (T P k2 K : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x acc => Bool.rec (Nat.lor acc (Nat.shiftLeft (nat_lit 1) x)) acc
      (isTree P (Nat.div x k2) (Nat.mod x k2) (t8 T x))) K

theorem gens_eq (T P k2 nc : ℕ) : gens T P k2 nc = gnRec T P k2 (nc * k2) := rfl

theorem gnRec_succ (T P k2 K : ℕ) : gnRec T P k2 (K + 1) =
    Bool.rec (Nat.lor (gnRec T P k2 K) (Nat.shiftLeft 1 K)) (gnRec T P k2 K)
      (isTree P (K / k2) (K % k2) (t8 T K)) := rfl

theorem gens_testBit (T P k2 nc x : ℕ) :
    (gens T P k2 nc).testBit x = true ↔ x < nc * k2 ∧ isTree P (x / k2) (x % k2) (t8 T x) = false := by
  rw [gens_eq]
  generalize nc * k2 = K
  induction K with
  | zero => simp [gnRec]
  | succ K ih =>
    rw [gnRec_succ]
    cases hK : isTree P (K / k2) (K % k2) (t8 T K)
    · change (gnRec T P k2 K ||| (1 <<< K)).testBit x = true ↔ _
      rw [Nat.testBit_or, Bool.or_eq_true, ih, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow,
        decide_eq_true_iff]
      constructor
      · rintro (⟨h1, h2⟩ | rfl)
        · exact ⟨by omega, h2⟩
        · exact ⟨by omega, hK⟩
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h1 | h1
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr h1.symm
    · change (gnRec T P k2 K).testBit x = true ↔ _
      rw [ih]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h1 | h1
        · exact ⟨h1, h2⟩
        · subst h1
          rw [hK] at h2
          exact absurd h2 (by decide)

@[expose] noncomputable def renL (N l : ℕ) : ℕ := 2 * (lt N (l / 2) - 1) + l % 2

@[expose] noncomputable def rnRec (N G w k : ℕ) : Bool × ℕ :=
  Nat.rec (motive := fun _ => Bool × Nat) (Prod.mk true (nat_lit 0))
    (fun i acc => Prod.rec (motive := fun _ => Bool × Nat) (fun ok a =>
      Prod.mk (mAnd ok (mAnd (live G (Nat.shiftRight (lt w i) (nat_lit 1)))
          (Nat.blt (nat_lit 0) (lt N (Nat.shiftRight (lt w i) (nat_lit 1))))))
        (Nat.lor a (Nat.shiftLeft
          (Nat.add (Nat.mul (nat_lit 2) (Nat.sub (lt N (Nat.shiftRight (lt w i) (nat_lit 1))) (nat_lit 1)))
            (Nat.land (lt w i) (nat_lit 1)))
          (Nat.mul (nat_lit 16) i)))) acc) k

theorem rename_eq (N G w n : ℕ) : rename N G w n = rnRec N G w n := rfl

theorem rnRec_succ (N G w k : ℕ) : rnRec N G w (k + 1) =
    Prod.rec (motive := fun _ => Bool × Nat) (fun ok a =>
      Prod.mk (mAnd ok (mAnd (live G (Nat.shiftRight (lt w k) (nat_lit 1)))
          (Nat.blt (nat_lit 0) (lt N (Nat.shiftRight (lt w k) (nat_lit 1))))))
        (Nat.lor a (Nat.shiftLeft
          (Nat.add (Nat.mul (nat_lit 2) (Nat.sub (lt N (Nat.shiftRight (lt w k) (nat_lit 1))) (nat_lit 1)))
            (Nat.land (lt w k) (nat_lit 1)))
          (Nat.mul (nat_lit 16) k)))) (rnRec N G w k) := rfl

theorem land1_eq (x : ℕ) : Nat.land x 1 = x % 2 := Nat.and_one_is_mod x

theorem rnRec_spec (N G w : ℕ) (hb : ∀ l, G.testBit (l / 2) = true → 0 < lt N (l / 2) → renL N l < 2 ^ 16) :
    ∀ k, (rnRec N G w k).1 = true →
      (∀ i < k, G.testBit (lt w i / 2) = true ∧ 0 < lt N (lt w i / 2)) ∧
        (rnRec N G w k).2 = enc ((wl w k).map (renL N)) := by
  intro k
  induction k with
  | zero => intro _; exact ⟨fun i hi => absurd hi (by omega), rfl⟩
  | succ k ih =>
    intro h
    rw [rnRec_succ] at h ⊢
    generalize hq : rnRec N G w k = q at ih h ⊢
    obtain ⟨ok, a⟩ := q
    dsimp only at h ⊢
    rw [mAnd_iff, mAnd_iff, live_iff, blt_iff, shr1_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨ih1, ih2⟩ := ih h1
    have hok : Ok16 ((wl w k).map (renL N)) := by
      intro d hd
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hd
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hl
      have := ih1 i (List.mem_range.1 hi)
      exact hb _ this.1 this.2
    refine ⟨fun i hi => ?_, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · exact ih1 i hi
      · rw [hi]
        exact ⟨h2, h3⟩
    · simp only at ih2
      rw [ih2, wl_succ, List.map_append, List.map_singleton, shr1_eq, land1_eq]
      have e := enc_concat (B := [renL N (lt w k)]) hok
      simp only [enc, Nat.mul_zero, Nat.add_zero, List.length_map, wl_length] at e
      rw [← e]
      rfl

@[expose] noncomputable def crRec (N G kq : ℕ) (k : ℕ) : Bool × ℕ :=
  Nat.rec (motive := fun _ => Bool × Nat) (Prod.mk true (nat_lit 0))
    (fun g acc => Prod.rec (motive := fun _ => Bool × Nat) (fun ok im =>
      Bool.rec (Prod.mk ok im)
        (Prod.mk
          (mAnd ok (mAnd (Nat.blt (nat_lit 0) (lt N g)) (mAnd (Nat.ble (lt N g) kq)
            (Nat.beq (Nat.land im (Nat.shiftLeft (nat_lit 1) (Nat.sub (lt N g) (nat_lit 1))))
              (nat_lit 0)))))
          (Nat.lor im (Nat.shiftLeft (nat_lit 1) (Nat.sub (lt N g) (nat_lit 1)))))
        (live G g)) acc) k

theorem chkRen_eq (N G ng kq : ℕ) : chkRen N G ng kq =
    Prod.rec (motive := fun _ => Bool)
      (fun ok im => mAnd ok (mAnd (Nat.blt G (Nat.shiftLeft (nat_lit 1) ng))
        (Nat.beq im (Nat.sub (Nat.shiftLeft (nat_lit 1) kq) (nat_lit 1))))) (crRec N G kq ng) := rfl

theorem crRec_succ (N G kq k : ℕ) : crRec N G kq (k + 1) =
    Prod.rec (motive := fun _ => Bool × Nat) (fun ok im =>
      Bool.rec (Prod.mk ok im)
        (Prod.mk
          (mAnd ok (mAnd (Nat.blt (nat_lit 0) (lt N k)) (mAnd (Nat.ble (lt N k) kq)
            (Nat.beq (Nat.land im (Nat.shiftLeft (nat_lit 1) (Nat.sub (lt N k) (nat_lit 1))))
              (nat_lit 0)))))
          (Nat.lor im (Nat.shiftLeft (nat_lit 1) (Nat.sub (lt N k) (nat_lit 1)))))
        (live G k)) (crRec N G kq k) := rfl

theorem land_pow_eq_zero {im t : ℕ} (h : Nat.land im (Nat.shiftLeft 1 t) = 0) : im.testBit t = false := by
  have h1 := congrArg (fun z => z.testBit t) h
  change (im &&& (1 <<< t)).testBit t = (0 : ℕ).testBit t at h1
  rw [Nat.testBit_and, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_self, Bool.and_true,
    Nat.zero_testBit] at h1
  exact h1

theorem crRec_spec (N G kq : ℕ) : ∀ k, (crRec N G kq k).1 = true →
    (∀ g < k, G.testBit g = true → 0 < lt N g ∧ lt N g ≤ kq) ∧
    (∀ g < k, ∀ g' < k, G.testBit g = true → G.testBit g' = true → lt N g = lt N g' → g = g') ∧
    ∀ t, (crRec N G kq k).2.testBit t = true ↔ ∃ g < k, G.testBit g = true ∧ lt N g - 1 = t := by
  intro k
  induction k with
  | zero => intro _; refine ⟨fun g hg => absurd hg (by omega), fun g hg => absurd hg (by omega), ?_⟩
            intro t
            simp [crRec]
  | succ k ih =>
    intro h
    rw [crRec_succ] at h ⊢
    generalize hq : crRec N G kq k = q at ih h ⊢
    obtain ⟨ok, im⟩ := q
    dsimp only at h ⊢
    cases hl : live G k
    · rw [hl] at h
      dsimp only at h ⊢
      have hk : G.testBit k = false := by
        rw [← Bool.not_eq_true, ← live_iff, hl]
        decide
      obtain ⟨i1, i2, i3⟩ := ih h
      refine ⟨fun g hg hG => ?_, fun g hg g' hg' hG hG' he => ?_, fun t => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hg | hg
        · exact i1 g hg hG
        · rw [hg, hk] at hG
          exact absurd hG (by decide)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hg | hg
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hg' with hg' | hg'
          · exact i2 g hg g' hg' hG hG' he
          · rw [hg', hk] at hG'
            exact absurd hG' (by decide)
        · rw [hg, hk] at hG
          exact absurd hG (by decide)
      · rw [i3]
        constructor
        · rintro ⟨g, hg, h1, h2⟩
          exact ⟨g, by omega, h1, h2⟩
        · rintro ⟨g, hg, h1, h2⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hg | hg
          · exact ⟨g, hg, h1, h2⟩
          · rw [hg, hk] at h1
            exact absurd h1 (by decide)
    · rw [hl] at h
      dsimp only at h ⊢
      rw [mAnd_iff, mAnd_iff, mAnd_iff, blt_iff, ble_iff, beq_iff] at h
      obtain ⟨h0, h1, h2, h3⟩ := h
      have hk : G.testBit k = true := (live_iff G k).1 hl
      have hfree : im.testBit (lt N k - 1) = false := land_pow_eq_zero h3
      obtain ⟨i1, i2, i3⟩ := ih h0
      refine ⟨fun g hg hG => ?_, fun g hg g' hg' hG hG' he => ?_, fun t => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hg | hg
        · exact i1 g hg hG
        · rw [hg]
          exact ⟨h1, h2⟩
      · have key : ∀ g < k, G.testBit g = true → lt N g ≠ lt N k := by
          intro g hg hG he
          have : im.testBit (lt N k - 1) = true := (i3 _).2 ⟨g, hg, hG, by rw [he]⟩
          rw [hfree] at this
          exact absurd this (by decide)
        rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hg | hg
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hg' with hg' | hg'
          · exact i2 g hg g' hg' hG hG' he
          · rw [hg'] at he
            exact absurd he (key g hg hG)
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hg' with hg' | hg'
          · rw [hg] at he
            exact absurd he.symm (key g' hg' hG')
          · rw [hg, hg']
      · change (im ||| (1 <<< (lt N k - 1))).testBit t = true ↔ _
        rw [Nat.testBit_or, Bool.or_eq_true, i3, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow,
          decide_eq_true_iff]
        constructor
        · rintro (⟨g, hg, h1, h2⟩ | h)
          · exact ⟨g, by omega, h1, h2⟩
          · exact ⟨k, by omega, hk, h⟩
        · rintro ⟨g, hg, hG, he⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hg | hg
          · exact Or.inl ⟨g, hg, hG, he⟩
          · rw [hg] at he
            exact Or.inr he

@[expose] noncomputable def nxF (N G : ℕ) (L B : List ℕ) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun B => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) B)
    (fun ha _ ih => fun B =>
      Bool.rec
        (List.rec (motive := fun _ => Bool) false (fun hb tb _ =>
          Prod.rec (motive := fun _ => Bool) (fun ok a =>
            mAnd ok (mAnd (Nat.beq (pk a (pn ha)) hb) (ih tb))) (rename N G (pw ha) (pn ha))) B)
        (ih B)
        (Nat.beq (pn ha) (nat_lit 0))) L B

theorem chkNext_eq (N : ℕ) (L B : List ℕ) (G ng kq : ℕ) :
    chkNext N L B G ng kq = mAnd (chkRen N G ng kq) (nxF N G L B) := rfl

theorem nxF_spec (N G : ℕ) : ∀ (L B : List ℕ), nxF N G L B = true →
    ∀ hb ∈ B, ∃ ha ∈ L, (rename N G (pw ha) (pn ha)).1 = true ∧
      hb = pk (rename N G (pw ha) (pn ha)).2 (pn ha) := by
  intro L
  induction L with
  | nil =>
    intro B h hb hhb
    cases B with
    | nil => simp at hhb
    | cons _ _ =>
      change false = true at h
      exact absurd h (by decide)
  | cons ha t ih =>
    intro B h hb hhb
    change Bool.rec _ (nxF N G t B) (Nat.beq (pn ha) 0) = true at h
    cases hz : Nat.beq (pn ha) 0
    · rw [hz] at h
      change List.rec (motive := fun _ => Bool) false (fun hb tb _ =>
          Prod.rec (motive := fun _ => Bool) (fun ok a =>
            mAnd ok (mAnd (Nat.beq (pk a (pn ha)) hb) (nxF N G t tb))) (rename N G (pw ha) (pn ha))) B
          = true at h
      cases B with
      | nil =>
        change false = true at h
        exact absurd h (by decide)
      | cons b tb =>
        change Prod.rec (motive := fun _ => Bool) (fun ok a =>
            mAnd ok (mAnd (Nat.beq (pk a (pn ha)) b) (nxF N G t tb))) (rename N G (pw ha) (pn ha))
            = true at h
        generalize hr : rename N G (pw ha) (pn ha) = r at h
        obtain ⟨ok, a⟩ := r
        dsimp only at h
        rw [mAnd_iff, mAnd_iff, beq_iff] at h
        rcases List.mem_cons.1 hhb with rfl | hhb
        · exact ⟨ha, List.mem_cons_self .., by rw [hr]; exact h.1, by rw [hr]; exact h.2.1.symm⟩
        · obtain ⟨ha', h1, h2⟩ := ih tb h.2.2 hb hhb
          exact ⟨ha', List.mem_cons_of_mem _ h1, h2⟩
    · rw [hz] at h
      obtain ⟨ha', h1, h2⟩ := ih B h hb hhb
      exact ⟨ha', List.mem_cons_of_mem _ h1, h2⟩

@[expose] noncomputable def trBody (T P k2 w i : ℕ) (acc : ℕ × (ℕ × ℕ)) : ℕ × (ℕ × ℕ) :=
  Prod.rec (motive := fun _ => Nat × (Nat × Nat)) (fun cur wm =>
    Prod.mk (t8 T (Nat.add (Nat.mul cur k2) (lt w i)))
      (Bool.rec
        (Prod.rec (motive := fun _ => Nat × Nat) (fun a m =>
          push a m (Nat.mul (nat_lit 2) (Nat.add (Nat.mul cur k2) (lt w i)))) wm)
        wm
        (isTree P cur (lt w i) (t8 T (Nat.add (Nat.mul cur k2) (lt w i)))))) acc

@[expose] noncomputable def trRec (T P k2 w c k : ℕ) : ℕ × (ℕ × ℕ) :=
  Nat.rec (motive := fun _ => Nat × (Nat × Nat)) (Prod.mk c (Prod.mk (nat_lit 0) (nat_lit 0)))
    (fun i acc => trBody T P k2 w i acc) k

theorem trace_eq (T P k2 w n c : ℕ) : trace T P k2 w n c = trRec T P k2 w c n := rfl

theorem trRec_succ (T P k2 w c k : ℕ) : trRec T P k2 w c (k + 1) = trBody T P k2 w k (trRec T P k2 w c k) :=
  rfl

@[expose] noncomputable def tsRec (T P k2 nc x : ℕ) (acc : Bool × List ℕ) (k : ℕ) : Bool × List ℕ :=
  Nat.rec (motive := fun _ => Bool × List Nat) acc
    (fun i s => Prod.rec (motive := fun _ => Bool × List Nat) (fun ok L =>
      Prod.rec (motive := fun _ => Bool × List Nat) (fun e wm =>
        Prod.mk (mAnd ok (Nat.beq e (Nat.sub (Nat.sub nc i) (nat_lit 1))))
          (List.cons (Prod.rec (motive := fun _ => Nat) pk wm) L))
        (trace T P k2 (pw x) (pn x) (Nat.sub (Nat.sub nc i) (nat_lit 1)))) s) k

theorem traces_eq (T P k2 nc x : ℕ) (acc : Bool × List ℕ) : traces T P k2 nc x acc = tsRec T P k2 nc x acc nc :=
  rfl

@[expose] def Closes (T P k2 nc x y : ℕ) : Prop :=
  ∃ c < nc, (trace T P k2 (pw x) (pn x) c).1 = c ∧
    y = pk (trace T P k2 (pw x) (pn x) c).2.1 (trace T P k2 (pw x) (pn x) c).2.2

theorem tsRec_spec (T P k2 nc x : ℕ) (ok0 : Bool) (L0 : List ℕ) : ∀ k ≤ nc,
    (tsRec T P k2 nc x (ok0, L0) k).1 = true →
      ok0 = true ∧ ∀ y ∈ (tsRec T P k2 nc x (ok0, L0) k).2, y ∈ L0 ∨ Closes T P k2 nc x y := by
  intro k
  induction k with
  | zero => intro _ h; exact ⟨h, fun y hy => Or.inl hy⟩
  | succ k ih =>
    intro hk h
    change (Prod.rec (motive := fun _ => Bool × List Nat) (fun ok L =>
      Prod.rec (motive := fun _ => Bool × List Nat) (fun e wm =>
        Prod.mk (mAnd ok (Nat.beq e (Nat.sub (Nat.sub nc k) (nat_lit 1))))
          (List.cons (Prod.rec (motive := fun _ => Nat) pk wm) L))
        (trace T P k2 (pw x) (pn x) (Nat.sub (Nat.sub nc k) (nat_lit 1))))
        (tsRec T P k2 nc x (ok0, L0) k)).1 = true at h
    change ok0 = true ∧ ∀ y ∈ (Prod.rec (motive := fun _ => Bool × List Nat) (fun ok L =>
      Prod.rec (motive := fun _ => Bool × List Nat) (fun e wm =>
        Prod.mk (mAnd ok (Nat.beq e (Nat.sub (Nat.sub nc k) (nat_lit 1))))
          (List.cons (Prod.rec (motive := fun _ => Nat) pk wm) L))
        (trace T P k2 (pw x) (pn x) (Nat.sub (Nat.sub nc k) (nat_lit 1))))
        (tsRec T P k2 nc x (ok0, L0) k)).2, y ∈ L0 ∨ Closes T P k2 nc x y
    generalize hq : tsRec T P k2 nc x (ok0, L0) k = q at ih h ⊢
    obtain ⟨ok, L⟩ := q
    generalize ht : trace T P k2 (pw x) (pn x) (Nat.sub (Nat.sub nc k) 1) = t at h ⊢
    obtain ⟨e, wm⟩ := t
    dsimp only at h ⊢
    rw [mAnd_iff, beq_iff] at h
    obtain ⟨ih1, ih2⟩ := ih (by omega) h.1
    refine ⟨ih1, fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · refine Or.inr ⟨nc - k - 1, by omega, ?_, ?_⟩
      · change (trace T P k2 (pw x) (pn x) (Nat.sub (Nat.sub nc k) 1)).1 = _
        rw [ht]
        exact h.2
      · change _ = pk (trace T P k2 (pw x) (pn x) (Nat.sub (Nat.sub nc k) 1)).2.1
          (trace T P k2 (pw x) (pn x) (Nat.sub (Nat.sub nc k) 1)).2.2
        rw [ht]
    · exact ih2 y hy

theorem allTraces_spec (T P k2 nc : ℕ) (W : List ℕ) :
    (List.rec (motive := fun _ => Bool × List Nat) (Prod.mk true List.nil)
      (fun h _ ih => Prod.rec (motive := fun _ => Bool × List Nat) (fun ok L =>
        Prod.rec (motive := fun _ => Bool × List Nat) (fun ok' L' => Prod.mk (mAnd ok ok') (appR L' L))
          (traces T P k2 nc h (Prod.mk true List.nil))) ih) W).1 = true →
    ∀ y ∈ (List.rec (motive := fun _ => Bool × List Nat) (Prod.mk true List.nil)
      (fun h _ ih => Prod.rec (motive := fun _ => Bool × List Nat) (fun ok L =>
        Prod.rec (motive := fun _ => Bool × List Nat) (fun ok' L' => Prod.mk (mAnd ok ok') (appR L' L))
          (traces T P k2 nc h (Prod.mk true List.nil))) ih) W).2,
      ∃ x ∈ W, Closes T P k2 nc x y := by
  induction W with
  | nil => intro _ y hy; simp at hy
  | cons x W ih =>
    intro h y hy
    generalize hq : (List.rec (motive := fun _ => Bool × List Nat) (Prod.mk true List.nil)
      (fun h _ ih => Prod.rec (motive := fun _ => Bool × List Nat) (fun ok L =>
        Prod.rec (motive := fun _ => Bool × List Nat) (fun ok' L' => Prod.mk (mAnd ok ok') (appR L' L))
          (traces T P k2 nc h (Prod.mk true List.nil))) ih) W) = q at ih
    change (Prod.rec (motive := fun _ => Bool × List Nat) (fun ok L =>
        Prod.rec (motive := fun _ => Bool × List Nat) (fun ok' L' => Prod.mk (mAnd ok ok') (appR L' L))
          (traces T P k2 nc x (Prod.mk true List.nil))) _).1 = true at h
    change y ∈ (Prod.rec (motive := fun _ => Bool × List Nat) (fun ok L =>
        Prod.rec (motive := fun _ => Bool × List Nat) (fun ok' L' => Prod.mk (mAnd ok ok') (appR L' L))
          (traces T P k2 nc x (Prod.mk true List.nil))) _).2 at hy
    rw [hq] at h hy
    obtain ⟨ok, L⟩ := q
    generalize ht : traces T P k2 nc x (true, []) = t at h hy
    obtain ⟨ok', L'⟩ := t
    dsimp only at h hy ih
    rw [mAnd_iff] at h
    rw [appR_eq] at hy
    rcases List.mem_append.1 hy with hy | hy
    · have := tsRec_spec T P k2 nc x true [] nc (le_refl _)
      rw [← traces_eq, ht] at this
      rcases (this h.2).2 y hy with hy | hy
      · simp at hy
      · exact ⟨x, List.mem_cons_self .., hy⟩
    · obtain ⟨x', h1, h2⟩ := ih h.1 y hy
      exact ⟨x', List.mem_cons_of_mem _ h1, h2⟩

theorem allTraces_mem {T P k2 nc : ℕ} {R : List ℕ} (h : (allTraces T P k2 nc R).1 = true) :
    ∀ y ∈ (allTraces T P k2 nc R).2, ∃ x ∈ R ++ invWords k2, Closes T P k2 nc x y := by
  intro y hy
  obtain ⟨x, hx, hc⟩ := allTraces_spec T P k2 nc (appR R (invWords k2)) h y hy
  exact ⟨x, by rwa [appR_eq] at hx, hc⟩

theorem invWords_mem (k2 : ℕ) : ∀ y ∈ invWords k2, ∃ l < k2,
    y = pk (Nat.lor l (Nat.shiftLeft (Nat.xor l 1) 16)) 2 := by
  unfold invWords
  suffices ∀ j ≤ k2, ∀ y ∈ Nat.rec (motive := fun _ => List Nat) List.nil
      (fun i acc => List.cons (pk (Nat.lor (Nat.sub (Nat.sub k2 i) (nat_lit 1))
        (Nat.shiftLeft (Nat.xor (Nat.sub (Nat.sub k2 i) (nat_lit 1)) (nat_lit 1)) (nat_lit 16)))
        (nat_lit 2)) acc) j, ∃ l < k2, y = pk (Nat.lor l (Nat.shiftLeft (Nat.xor l 1) 16)) 2 from
    this k2 (le_refl _)
  intro j
  induction j with
  | zero => intro _ y hy; simp at hy
  | succ j ih =>
    intro hj y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨k2 - j - 1, by omega, rfl⟩
    · exact ih (by omega) y hy

end CFSG.KM24.RS

end
