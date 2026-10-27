module

public import Certificates.Data.Kernel.SmithEKC
public import CFSG.Certificates.Kernel.SmithEK.TSound
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.SmithE.K

open CFSG.F4.Native CFSG.SmithE

theorem testBit_fld (s X j : Nat) :
    (fld s X).testBit j = (decide (j < 20) && X.testBit (20 * s + j)) := by
  unfold fld
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm j]

theorem fld_and (s X Y : Nat) : fld s (X &&& Y) = fld s X &&& fld s Y := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, testBit_fld, testBit_fld, testBit_fld, Nat.testBit_and]
  cases decide (j < 20) <;> simp

theorem fld_lt (s X : Nat) : fld s X < 2 ^ 20 := Nat.mod_lt _ (by positivity)

theorem fld_cons20 {x : Nat} (hx : x < 2 ^ 20) (y s : Nat) :
    fld 0 (x + 2 ^ 20 * y) = x ∧ fld (s + 1) (x + 2 ^ 20 * y) = fld s y := by
  constructor
  · unfold fld
    rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  · unfold fld
    rw [show 20 * (s + 1) = 20 + 20 * s by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx, Nat.zero_add]

theorem fld_add20 (s X : Nat) : fld (s + 20) X = fld s (X / 2 ^ 400) := by
  unfold fld
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, show 400 + 20 * s = 20 * (s + 20) by ring]

theorem fld_block {x : Nat} (hx : x < 2 ^ 400) (y : Nat) {t : Nat} (ht : t < 20) :
    fld t (x + 2 ^ 400 * y) = fld t x ∧
      ∀ l, fld (20 * (l + 1) + t) (x + 2 ^ 400 * y) = fld (20 * l + t) y := by
  constructor
  · apply Nat.eq_of_testBit_eq
    intro j
    rw [testBit_fld, testBit_fld]
    by_cases hj : j < 20
    · have hlt : 20 * t + j < 400 := by omega
      have h1 : (x + 2 ^ 400 * y) % 2 ^ 400 = x := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
      have e := Nat.testBit_mod_two_pow (x + 2 ^ 400 * y) 400 (20 * t + j)
      rw [h1] at e
      simp only [hj, decide_true, Bool.true_and]
      rw [e]
      simp [hlt]
    · simp [hj]
  · intro l
    have h2 : (x + 2 ^ 400 * y) / 2 ^ 400 = y := by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx, Nat.zero_add]
    rw [show 20 * (l + 1) + t = 20 * l + t + 20 by ring, fld_add20, h2]

theorem pkW_cons (w x : Nat) (L : List Nat) : pkW w (x :: L) = x + 2 ^ w * pkW w L := by
  change x + (pkW w L <<< w) = _
  rw [Nat.shiftLeft_eq, Nat.mul_comm]

theorem pkW_nil (w : Nat) : pkW w [] = 0 := rfl

theorem pkW_lt {w : Nat} : ∀ (L : List Nat), (∀ x ∈ L, x < 2 ^ w) → pkW w L < 2 ^ (w * L.length)
  | [], _ => by simp [pkW_nil]
  | x :: L, h => by
    rw [pkW_cons, List.length_cons, Nat.mul_succ, Nat.pow_add]
    have h1 := h x List.mem_cons_self
    have h2 := pkW_lt L fun y hy => h y (List.mem_cons_of_mem _ hy)
    calc x + 2 ^ w * pkW w L < 2 ^ w + 2 ^ w * pkW w L := by omega
      _ = 2 ^ w * (pkW w L + 1) := by ring
      _ ≤ 2 ^ w * 2 ^ (w * L.length) := Nat.mul_le_mul_left _ h2
      _ = 2 ^ (w * L.length) * 2 ^ w := Nat.mul_comm _ _

theorem fld_pkW20 : ∀ (L : List Nat) (s : Nat), (∀ x ∈ L, x < 2 ^ 20) →
    fld s (pkW 20 L) = L.getD s 0
  | [], s, _ => by rw [pkW_nil, fld_zero]; simp
  | x :: L, s, h => by
    have hx := h x List.mem_cons_self
    rw [pkW_cons]
    rcases s with _ | s
    · rw [(fld_cons20 hx _ 0).1, List.getD_cons_zero]
    · rw [(fld_cons20 hx _ s).2, List.getD_cons_succ]
      exact fld_pkW20 L s fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem fld_pkW400 : ∀ (L : List Nat) (l t : Nat), t < 20 → (∀ x ∈ L, x < 2 ^ 400) →
    fld (20 * l + t) (pkW 400 L) = fld t (L.getD l 0)
  | [], l, t, _, _ => by rw [pkW_nil, fld_zero]; simp [fld_zero]
  | x :: L, l, t, ht, h => by
    have hx := h x List.mem_cons_self
    rw [pkW_cons]
    rcases l with _ | l
    · rw [Nat.mul_zero, Nat.zero_add, (fld_block hx _ ht).1, List.getD_cons_zero]
    · rw [(fld_block hx _ ht).2 l, List.getD_cons_succ]
      exact fld_pkW400 L l t ht fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem pkW_rep_mul (x : Nat) : ∀ n, pkW 400 (List.replicate n 1) * x =
    pkW 400 (List.replicate n x)
  | 0 => by simp [pkW_nil]
  | n + 1 => by
    rw [List.replicate_succ, List.replicate_succ, pkW_cons, pkW_cons, ← pkW_rep_mul x n]
    ring

theorem fld_mul_spread {a : Nat} (ha : a < 2 ^ 20) : ∀ (M : Nat), (∀ s, fld s M ≤ 1) →
    ∀ s, fld s (M * a) = fld s M * a := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro hM s
    rcases Nat.eq_zero_or_pos M with h0 | hpos
    · subst h0
      rw [Nat.zero_mul, fld_zero, Nat.zero_mul]
    · have e : M = M % 2 ^ 20 + 2 ^ 20 * (M / 2 ^ 20) := (Nat.mod_add_div M (2 ^ 20)).symm
      have hm0 : M % 2 ^ 20 ≤ 1 := by
        have := hM 0
        unfold fld at this
        simpa using this
      have hm0lt : M % 2 ^ 20 < 2 ^ 20 := by omega
      have hlt : M % 2 ^ 20 * a < 2 ^ 20 :=
        lt_of_le_of_lt (le_trans (Nat.mul_le_mul_right a hm0) (by omega)) ha
      have eM : M * a = M % 2 ^ 20 * a + 2 ^ 20 * (M / 2 ^ 20 * a) := by
        conv_lhs => rw [e]
        ring
      have hl' : ∀ s, fld s (M / 2 ^ 20) ≤ 1 := fun s => by
        have := hM (s + 1)
        rw [e, (fld_cons20 hm0lt _ s).2] at this
        exact this
      rcases s with _ | s
      · rw [eM, (fld_cons20 hlt _ 0).1]
        conv_rhs => rw [e, (fld_cons20 hm0lt _ 0).1]
      · rw [eM, (fld_cons20 hlt _ s).2,
          ih (M / 2 ^ 20) (Nat.div_lt_self hpos (by norm_num)) hl' s]
        conv_rhs => rw [e, (fld_cons20 hm0lt _ s).2]

theorem applyL_congr_low : ∀ (A : List Nat) (c c' : Nat),
    (∀ j < A.length, c.testBit j = c'.testBit j) → applyL A c = applyL A c'
  | [], _, _, _ => rfl
  | x :: A, c, c', h => by
    have e : ∀ d, applyL (x :: A) d = (if d.testBit 0 then x else 0) ^^^ applyL A (d / 2) :=
      fun _ => rfl
    rw [e, e, h 0 (by simp), applyL_congr_low A (c / 2) (c' / 2) fun j hj => by
      rw [← Nat.testBit_succ, ← Nat.testBit_succ]
      exact h (j + 1) (by simp; omega)]

theorem fld_shr1 (s Z : Nat) {j : Nat} (hj : j < 19) :
    (fld s (Z >>> 1)).testBit j = (fld s Z / 2).testBit j := by
  rw [← Nat.testBit_succ, testBit_fld, testBit_fld, Nat.testBit_shiftRight]
  have h1 : j < 20 := by omega
  have h2 : j + 1 < 20 := by omega
  simp only [h1, h2, decide_true, Bool.true_and]
  congr 1
  omega

theorem and_one_mul (x a : Nat) : (x &&& 1) * a = if x.testBit 0 then a else 0 := by
  rw [Nat.and_one_is_mod, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]

theorem fld_lmulP {ONE : Nat} (hO : ∀ s, fld s ONE ≤ 1) : ∀ (A : List Nat) (Z s : Nat),
    A.length ≤ 20 → (∀ a ∈ A, a < 2 ^ 20) → fld s ONE = 1 →
    fld s (lmulP ONE A Z) = applyL A (fld s Z)
  | [], _, s, _, _, _ => fld_zero s
  | a :: A, Z, s, hl, ha, hs => by
    have e1 : lmulP ONE (a :: A) Z = ((Z &&& ONE) * a) ^^^ lmulP ONE A (Z >>> 1) := rfl
    have e2 : ∀ d, applyL (a :: A) d = (if d.testBit 0 then a else 0) ^^^ applyL A (d / 2) :=
      fun _ => rfl
    have hlane : ∀ s, fld s (Z &&& ONE) ≤ 1 := fun s => by
      rw [fld_and]
      exact le_trans Nat.and_le_right (hO s)
    rw [e1, fld_xor, fld_mul_spread (ha a List.mem_cons_self) _ hlane, fld_and, hs, and_one_mul,
      fld_lmulP hO A (Z >>> 1) s (by simp at hl; omega)
        (fun b hb => ha b (List.mem_cons_of_mem _ hb)) hs, e2]
    congr 1
    exact applyL_congr_low A _ _ fun j hj => fld_shr1 s Z (by simp at hl; omega)

theorem fld_bmulP {ONE : Nat} (hO : ∀ s, fld s ONE ≤ 1) : ∀ (Qs : List Nat) (Z s : Nat),
    Qs.length ≤ 20 → fld s ONE = 1 →
    fld s (bmulP ONE Qs Z) = applyL (Qs.map (fld s)) (fld s Z)
  | [], _, s, _, _ => fld_zero s
  | q :: Qs, Z, s, hl, hs => by
    have e1 : bmulP ONE (q :: Qs) Z =
        (q &&& ((Z &&& ONE) * (2 ^ 20 - 1))) ^^^ bmulP ONE Qs (Z >>> 1) := rfl
    have e2 : ∀ (L : List Nat) (x d : Nat),
        applyL (x :: L) d = (if d.testBit 0 then x else 0) ^^^ applyL L (d / 2) := fun _ _ _ => rfl
    have hlane : ∀ s, fld s (Z &&& ONE) ≤ 1 := fun s => by
      rw [fld_and]
      exact le_trans Nat.and_le_right (hO s)
    rw [e1, fld_xor, fld_and, fld_mul_spread (by norm_num) _ hlane, fld_and, hs, and_one_mul,
      fld_bmulP hO Qs (Z >>> 1) s (by simp at hl; omega) hs, List.map_cons, e2]
    congr 1
    · split_ifs
      · rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (fld_lt _ _)]
      · rw [Nat.and_zero]
    · exact applyL_congr_low _ _ _ fun j hj => fld_shr1 s Z (by simp at hj hl; omega)

theorem l20_lt : l20 < 2 ^ 400 := by decide

theorem l20_mul : (2 ^ 20 - 1) * l20 = 2 ^ 400 - 1 := by decide

theorem mul_l20_lt {c : Nat} (hc : c < 2 ^ 20) : c * l20 < 2 ^ 400 := by
  have h1 : c * l20 ≤ (2 ^ 20 - 1) * l20 := Nat.mul_le_mul_right _ (by omega)
  rw [l20_mul] at h1
  have h2 : (0 : Nat) < 2 ^ 400 := by positivity
  omega

theorem fld_l20 (t : Nat) : fld t l20 = if t < 20 then 1 else 0 := by
  by_cases ht : t < 20
  · rw [if_pos ht]
    interval_cases t <;> decide
  · rw [if_neg ht]
    unfold fld
    rw [Nat.div_eq_of_lt (lt_of_lt_of_le l20_lt (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem getD_replicate_lt {x d n a : Nat} (ha : a < n) : (List.replicate n x).getD a d = x := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_replicate]; exact ha), List.getElem_replicate]

theorem getD_lt_of {c : List Nat} {B : Nat} (h : ∀ x ∈ c, x < B) (hB : 0 < B) (i : Nat) :
    c.getD i 0 < B := by
  by_cases hi : i < c.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact hB

theorem fld_div20 (s X : Nat) : fld s X = fld (20 * (s / 20) + s % 20) X := by
  rw [Nat.div_add_mod]

theorem fld_ONE (s : Nat) :
    fld s (pkW 400 (List.replicate 693 1) * l20) = if s < 13860 then 1 else 0 := by
  have hlt : ∀ x ∈ List.replicate 693 l20, x < 2 ^ 400 := fun x hx => by
    rw [List.eq_of_mem_replicate hx]
    exact l20_lt
  rw [pkW_rep_mul, fld_div20, fld_pkW400 _ _ _ (Nat.mod_lt _ (by norm_num)) hlt]
  by_cases hs : s < 13860
  · rw [getD_replicate_lt (by omega), fld_l20, if_pos (Nat.mod_lt _ (by norm_num)), if_pos hs]
  · rw [List.getD_eq_default _ _ (by rw [List.length_replicate]; omega), fld_zero, if_neg hs]

theorem fldsC_get : ∀ (n r : Nat), fldsC n r = true → ∀ a < n, (r >>> (10 * a)) % 1024 < 693
  | 0, _, _, a, ha => absurd ha (Nat.not_lt_zero a)
  | n + 1, r, h, a, ha => by
    have h' : (decide (r % 1024 < 693) && fldsC n (r >>> 10)) = true := h
    rw [Bool.and_eq_true, decide_eq_true_eq] at h'
    rcases a with _ | a
    · simpa using h'.1
    · rw [show 10 * (a + 1) = 10 + 10 * a by ring, Nat.shiftRight_add]
      exact fldsC_get n _ h'.2 a (by omega)

theorem fld_gathC (Bpk : Nat) : ∀ (n r a m : Nat), a < n → m < 20 →
    fld (20 * a + m) (gathC Bpk n r) = fld m (blkC Bpk ((r >>> (10 * a)) % 1024))
  | 0, _, a, _, ha, _ => absurd ha (Nat.not_lt_zero a)
  | n + 1, r, a, m, ha, hm => by
    have e : gathC Bpk (n + 1) r = blkC Bpk (r % 1024) + 2 ^ 400 * gathC Bpk n (r >>> 10) := by
      change blkC Bpk (r % 1024) + (gathC Bpk n (r >>> 10) <<< 400) = _
      rw [Nat.shiftLeft_eq, Nat.mul_comm]
    have hb : blkC Bpk (r % 1024) < 2 ^ 400 := Nat.mod_lt _ (by positivity)
    rw [e]
    rcases a with _ | a
    · have e0 : 20 * 0 + m = m := by omega
      have e1 : r >>> (10 * 0) = r := by simp
      rw [e0, e1, (fld_block hb _ hm).1]
    · rw [(fld_block hb _ hm).2 a, fld_gathC Bpk n _ a m (by omega) hm,
        show 10 * (a + 1) = 10 + 10 * a by ring, Nat.shiftRight_add]

theorem fld_blkC (X f m : Nat) (hm : m < 20) : fld m (blkC X f) = fld (20 * f + m) X := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_fld, testBit_fld]
  unfold blkC
  by_cases hj : j < 20
  · have h1 : 20 * m + j < 400 := by omega
    simp only [hj, decide_true, Bool.true_and, Nat.testBit_mod_two_pow, h1,
      Nat.testBit_shiftRight]
    congr 1
    ring
  · simp [hj]

theorem rowsC_get {ONE REP ID Bpk : Nat} {Qs : List Nat} {R : Nat → Nat} :
    ∀ (Cr : List (List Nat)) (Pr : List Nat) (j : Nat),
      rowsC ONE REP ID Bpk Qs R Cr Pr j = true → Pr = Cr.map (pkW 20) →
      ∀ i < Cr.length, rowC ONE REP ID Bpk Qs (Cr.getD i []) (pkW 20 (Cr.getD i []))
        (R (j + i)) = true
  | [], _, _, _, _, i, hi => absurd hi (by simp)
  | A :: Cr, Pr, j, h, hP, i, hi => by
    subst hP
    have h' : (rowC ONE REP ID Bpk Qs A (pkW 20 A) (R j) &&
        rowsC ONE REP ID Bpk Qs R Cr (Cr.map (pkW 20)) (j + 1)) = true := h
    rw [Bool.and_eq_true] at h'
    rcases i with _ | i
    · simpa using h'.1
    · have e := rowsC_get Cr _ (j + 1) h'.2 rfl i (by simpa using hi)
      rw [List.getD_cons_succ, show j + (i + 1) = j + 1 + i by omega]
      exact e

theorem rowsC_lanes {C : List (List Nat)} {R : Nat → Nat} (hl : C.length = 693)
    (hc : ∀ k < 693, (C.getD k []).length = 20 ∧ ∀ m < 20, (C.getD k []).getD m 0 < 2 ^ 20)
    (h : rowsC (pkW 400 (List.replicate 693 1) * l20) (pkW 400 (List.replicate 693 1))
      (pkW 20 ((List.range 20).map (2 ^ ·))) (pkW 400 (C.map (pkW 20))) (qsOf C) R C
      (C.map (pkW 20)) 0 = true) :
    ∀ j < 693, (∀ m < 20, applyL (C.getD j []) ((C.getD j []).getD m 0) = 2 ^ m) ∧
      ∀ a < 693, fldR R j a < 693 ∧ ∀ m < 20,
        applyL (C.getD j []) (applyL (C.getD a []) ((C.getD j []).getD m 0)) =
          (C.getD (fldR R j a) []).getD m 0 := by
  intro j hj
  have hmemC : ∀ c ∈ C, c.length = 20 ∧ ∀ x ∈ c, x < 2 ^ 20 := by
    intro c hcm
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hcm
    have e := hc k (by omega)
    rw [List.getD_eq_getElem _ _ hk] at e
    refine ⟨e.1, fun x hx => ?_⟩
    obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hx
    have := e.2 m (by omega)
    rwa [List.getD_eq_getElem _ _ hm] at this
  have hO : ∀ s, fld s (pkW 400 (List.replicate 693 1) * l20) ≤ 1 := fun s => by
    rw [fld_ONE]
    split_ifs <;> omega
  have hO1 : ∀ s < 13860, fld s (pkW 400 (List.replicate 693 1) * l20) = 1 := fun s hs => by
    rw [fld_ONE, if_pos hs]
  have hrow := rowsC_get C _ 0 h rfl j (by omega)
  rw [Nat.zero_add] at hrow
  have hAm : C.getD j [] ∈ C := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  generalize hA : C.getD j [] = A at hrow hAm ⊢
  obtain ⟨hAl, hAb⟩ := hmemC A hAm
  unfold rowC at hrow
  simp only [Bool.and_eq_true, beq_iff_eq] at hrow
  obtain ⟨⟨e1, e2⟩, e3⟩ := hrow
  have hAp : ∀ m < 20, fld m (pkW 20 A) = A.getD m 0 := fun m _ => fld_pkW20 A m hAb
  have hApl : pkW 20 A < 2 ^ 400 := by
    have := pkW_lt A hAb
    rwa [hAl] at this
  refine ⟨fun m hm => ?_, fun a ha => ?_⟩
  · have e := congrArg (fld m) e1
    rw [fld_lmulP hO A _ m (by omega) hAb (hO1 m (by omega)), hAp m hm,
      fld_pkW20 _ m (fun x hx => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        exact Nat.pow_lt_pow_right (by norm_num) (List.mem_range.mp hi))] at e
    rw [e]
    simp [List.getD_eq_getElem?_getD, hm]
  · have hf := fldsC_get 693 _ e2 a ha
    refine ⟨hf, fun m hm => ?_⟩
    have hs : 20 * a + m < 13860 := by omega
    have e := congrArg (fld (20 * a + m)) e3
    rw [fld_lmulP hO A _ _ (by omega) hAb (hO1 _ hs), fld_bmulP hO _ _ _ (by simp [qsOf])
      (hO1 _ hs), pkW_rep_mul, fld_pkW400 _ _ _ hm (fun x hx => by
        rw [List.eq_of_mem_replicate hx]; exact hApl), getD_replicate_lt ha, hAp m hm,
      fld_gathC _ 693 _ a m ha hm, fld_blkC _ _ _ hm] at e
    have hq : (qsOf C).map (fld (20 * a + m)) = C.getD a [] := by
      obtain ⟨hCl, hCb⟩ := hmemC (C.getD a []) (by
        rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
      apply List.ext_getElem (by unfold qsOf; rw [List.length_map, List.length_map, List.length_range, hCl])
      intro i h1 h2
      have hi : i < 20 := by simpa [qsOf] using h1
      simp only [qsOf, List.getElem_map, List.getElem_range]
      rw [fld_pkW400 _ _ _ hm (fun x hx => by
          obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hx
          exact mul_l20_lt (getD_lt_of (hmemC c hcm).2 (by positivity) i)),
        List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map,
        ← List.getD_eq_getElem _ [] (by omega), Nat.mul_comm,
        fld_mul_spread (getD_lt_of hCb (by positivity) i) _
          (fun t => by rw [fld_l20]; split_ifs <;> omega), fld_l20, if_pos hm, Nat.one_mul,
        List.getD_eq_getElem _ _ (by omega)]
    rw [hq] at e
    rw [e, fld_pkW400 _ _ _ hm (fun x hx => by
        obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hx
        obtain ⟨hcl, hcb⟩ := hmemC c hcm
        have := pkW_lt c hcb
        rwa [hcl] at this)]
    have hfC : (C.map (pkW 20)).getD (fldR R j a) 0 = pkW 20 (C.getD (fldR R j a) []) := by
      rw [List.getD_eq_getElem _ _ (by simp; unfold fldR; omega), List.getElem_map,
        List.getD_eq_getElem _ _ (by unfold fldR; omega)]
    unfold fldR at hfC ⊢
    rw [hfC, fld_pkW20 _ _ (hmemC _ (by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)).2]

end CFSG.SmithE.K
