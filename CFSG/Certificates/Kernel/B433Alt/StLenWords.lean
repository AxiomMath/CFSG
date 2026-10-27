module

public import Certificates.Data.Kernel.B433Alt.Trace
public import CFSG.Certificates.CosetEnumeration
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KC.B433Alt

open CFSG.Certificates.CosetEnumeration CFSG.KC.B4A CFSG.KC.Y333

theorem stL_sN (v : ℕ) (k : ℕ → ℕ) : sN v k = k v := by cases v <;> rfl

theorem stL_sB (v : ℕ) (k : ℕ → Bool) : sB v k = k v := by cases v <;> rfl

theorem stL_andB (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem stL_orB (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem stL_notB (a : Bool) : notB a = !a := by cases a <;> rfl

theorem stL_andB_eq_true {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andB]

theorem stL_rec_andB (f : ℕ → Bool) (n : ℕ) :
    Nat.rec (motive := fun _ => Bool) true (fun i acc => andB acc (f i)) n = true ↔
      ∀ i < n, f i = true := by
  induction n with
  | zero => simp
  | succ n ih =>
    show andB _ (f n) = true ↔ _
    rw [stL_andB_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h1 i h
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

theorem stL_lor_shiftLeft {x y m : ℕ} (hx : x < 2 ^ m) : x ||| (y <<< m) = x + 2 ^ m * y := by
  rw [Nat.shiftLeft_eq, Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hx,
    Nat.add_comm]

theorem stL_fld_eq (x o m : ℕ) : fld x o (2 ^ m - 1) = x / 2 ^ o % 2 ^ m := by
  show (x >>> o) &&& (2 ^ m - 1) = _
  rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]

theorem stL_two_pow_four_mul (n : ℕ) : (2 : ℕ) ^ (4 * n) = 16 ^ n := by
  rw [pow_mul]; norm_num

theorem stL_digit_add_lt {x y k j : ℕ} (hj : j < k) :
    (x + 16 ^ k * y) / 16 ^ j % 16 = x / 16 ^ j % 16 := by
  obtain ⟨d, rfl⟩ : ∃ d, k = j + 1 + d := ⟨k - j - 1, by omega⟩
  rw [show 16 ^ (j + 1 + d) * y = 16 ^ j * (16 * (16 ^ d * y)) by ring,
    Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

theorem stL_digit_add_ge {x y k j : ℕ} (hx : x < 16 ^ k) (hj : k ≤ j) :
    (x + 16 ^ k * y) / 16 ^ j % 16 = y / 16 ^ (j - k) % 16 := by
  obtain ⟨d, rfl⟩ : ∃ d, j = k + d := ⟨j - k, by omega⟩
  rw [pow_add, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt hx, zero_add, Nat.add_sub_cancel_left]

theorem stL_add_lt {x y k l : ℕ} (hx : x < 16 ^ k) (hy : y < 16 ^ l) :
    x + 16 ^ k * y < 16 ^ (k + l) := by
  rw [pow_add]
  calc x + 16 ^ k * y < 16 ^ k + 16 ^ k * y := by omega
    _ = 16 ^ k * (y + 1) := by ring
    _ ≤ 16 ^ k * 16 ^ l := Nat.mul_le_mul_left _ hy

theorem stL_wLen_eq (w : ℕ) : wLen w = w % 2 ^ 32 := by
  show w &&& 4294967295 = _
  rw [show (4294967295 : ℕ) = 2 ^ 32 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]

theorem stL_wStr_eq (w : ℕ) : wStr w = w / 2 ^ 32 := by
  show w >>> 32 = _
  rw [Nat.shiftRight_eq_div_pow]

theorem stL_wLen_lt (w : ℕ) : wLen w < 2 ^ 32 := by
  rw [stL_wLen_eq]; exact Nat.mod_lt _ (by positivity)

theorem stL_wMk_eq {n : ℕ} (s : ℕ) (hn : n < 2 ^ 32) : wMk n s = n + 2 ^ 32 * s := by
  show n ||| (s <<< 32) = _
  exact stL_lor_shiftLeft hn

theorem stL_wLen_wMk {n : ℕ} (s : ℕ) (hn : n < 2 ^ 32) : wLen (wMk n s) = n := by
  rw [stL_wLen_eq, stL_wMk_eq s hn, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hn]

theorem stL_wStr_wMk {n : ℕ} (s : ℕ) (hn : n < 2 ^ 32) : wStr (wMk n s) = s := by
  rw [stL_wStr_eq, stL_wMk_eq s hn, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt hn, zero_add]

theorem stL_wAt_eq (w i : ℕ) : wAt w i = wStr w / 16 ^ i % 16 := by
  show fld (wStr w) (4 * i) (2 ^ 4 - 1) = _
  rw [stL_fld_eq, stL_two_pow_four_mul]
  norm_num

theorem stL_wAt_lt (w i : ℕ) : wAt w i < 16 := by
  rw [stL_wAt_eq]; exact Nat.mod_lt _ (by norm_num)

theorem stL_wOK_iff (w : ℕ) : wOK w = true ↔ wStr w < 16 ^ wLen w := by
  show Nat.blt (wStr w) (1 <<< (4 * wLen w)) = true ↔ _
  rw [Nat.blt_eq, Nat.one_shiftLeft, stL_two_pow_four_mul]

theorem stL_wLen_zero : wLen 0 = 0 := by rw [stL_wLen_eq]; rfl

theorem stL_length_wList (w : ℕ) : (wList w).length = wLen w := by simp [wList]

theorem stL_getElem_wList (w i : ℕ) (h : i < (wList w).length) : (wList w)[i] = wAt w i := by
  simp [wList]

theorem stL_mem_wList {w c : ℕ} : c ∈ wList w ↔ ∃ i < wLen w, wAt w i = c := by
  simp [wList]

theorem stL_wList_zero : wList 0 = [] := by simp [wList, stL_wLen_zero]

theorem stL_wList_ext {v w : ℕ} (hl : wLen v = wLen w) (ha : ∀ i < wLen w, wAt v i = wAt w i) :
    wList v = wList w := by
  apply List.ext_getElem (by simp [stL_length_wList, hl])
  intro i h1 h2
  rw [stL_getElem_wList, stL_getElem_wList]
  exact ha i (by simpa [stL_length_wList] using h2)

theorem stL_wInH_iff (w : ℕ) : wInH w = true ↔ wOK w = true ∧ ∀ i < wLen w, wAt w i < 10 := by
  show andB (wOK w) (Nat.rec (motive := fun _ => Bool) true
    (fun i acc => andB acc (Nat.blt (wAt w i) 10)) (wLen w)) = true ↔ _
  rw [stL_andB_eq_true, stL_rec_andB]
  simp

theorem stL_wOK_of_wInH {w : ℕ} (h : wInH w = true) : wOK w = true := ((stL_wInH_iff w).1 h).1

theorem stL_wAt_lt_of_wInH {w : ℕ} (h : wInH w = true) : ∀ i < wLen w, wAt w i < 10 :=
  ((stL_wInH_iff w).1 h).2

theorem stL_lt_of_mem_wList {w c : ℕ} (h : wInH w = true) (hc : c ∈ wList w) : c < 10 := by
  obtain ⟨i, hi, rfl⟩ := stL_mem_wList.1 hc
  exact stL_wAt_lt_of_wInH h i hi

theorem stL_thm_lt {c : ℕ} (hc : c < 16) (h : fld THM (4 * c) 15 < 10) : c < 10 ∧ c ≠ 7 := by
  have key : ∀ c < 16, fld THM (4 * c) 15 < 10 → c < 10 ∧ c ≠ 7 := by decide +kernel
  exact key c hc h

theorem stL_thm_lt16 (c : ℕ) : fld THM (4 * c) 15 < 16 := by
  rw [show (15 : ℕ) = 2 ^ 4 - 1 by norm_num, stL_fld_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem stL_thm_of_lt {c : ℕ} (hc : c < 10) (h7 : c ≠ 7) : fld THM (4 * c) 15 < 10 := by
  have key : ∀ c < 10, c ≠ 7 → fld THM (4 * c) 15 < 10 := by decide +kernel
  exact key c hc h7

theorem stL_wInT_iff (w : ℕ) :
    wInT w = true ↔ wOK w = true ∧ ∀ i < wLen w, fld THM (4 * wAt w i) 15 < 10 := by
  show andB (wOK w) (Nat.rec (motive := fun _ => Bool) true
    (fun i acc => andB acc (Nat.blt (fld THM (4 * wAt w i) 15) 10)) (wLen w)) = true ↔ _
  rw [stL_andB_eq_true, stL_rec_andB]
  simp

theorem stL_wInH_of_wInT {w : ℕ} (h : wInT w = true) : wInH w = true := by
  obtain ⟨h1, h2⟩ := (stL_wInT_iff w).1 h
  exact (stL_wInH_iff w).2 ⟨h1, fun i hi => (stL_thm_lt (stL_wAt_lt w i) (h2 i hi)).1⟩

section
variable {a b : ℕ}

theorem stL_wCat_str (ha : wOK a = true) :
    wStr a ||| (wStr b <<< (4 * wLen a)) = wStr a + 16 ^ wLen a * wStr b := by
  rw [stL_lor_shiftLeft (by rw [stL_two_pow_four_mul]; exact (stL_wOK_iff a).1 ha),
    stL_two_pow_four_mul]

theorem stL_wLen_wCat (h : wLen a + wLen b < 2 ^ 32) : wLen (wCat a b) = wLen a + wLen b :=
  stL_wLen_wMk _ h

theorem stL_wStr_wCat (h : wLen a + wLen b < 2 ^ 32) (ha : wOK a = true) :
    wStr (wCat a b) = wStr a + 16 ^ wLen a * wStr b := by
  show wStr (wMk (wLen a + wLen b) (wStr a ||| (wStr b <<< (4 * wLen a)))) = _
  rw [stL_wStr_wMk _ h, stL_wCat_str ha]

theorem stL_wAt_wCat_lt (h : wLen a + wLen b < 2 ^ 32) (ha : wOK a = true) {i : ℕ}
    (hi : i < wLen a) : wAt (wCat a b) i = wAt a i := by
  rw [stL_wAt_eq, stL_wAt_eq, stL_wStr_wCat h ha, stL_digit_add_lt hi]

theorem stL_wAt_wCat_ge (h : wLen a + wLen b < 2 ^ 32) (ha : wOK a = true) {i : ℕ}
    (hi : wLen a ≤ i) : wAt (wCat a b) i = wAt b (i - wLen a) := by
  rw [stL_wAt_eq, stL_wAt_eq, stL_wStr_wCat h ha, stL_digit_add_ge ((stL_wOK_iff a).1 ha) hi]

theorem stL_wOK_wCat (h : wLen a + wLen b < 2 ^ 32) (ha : wOK a = true) (hb : wOK b = true) :
    wOK (wCat a b) = true := by
  rw [stL_wOK_iff, stL_wStr_wCat h ha, stL_wLen_wCat h]
  exact stL_add_lt ((stL_wOK_iff a).1 ha) ((stL_wOK_iff b).1 hb)

theorem stL_wList_wCat (h : wLen a + wLen b < 2 ^ 32) (ha : wOK a = true) :
    wList (wCat a b) = wList a ++ wList b := by
  apply List.ext_getElem (by simp [stL_length_wList, stL_wLen_wCat h])
  intro i h1 h2
  rw [stL_getElem_wList, List.getElem_append]
  split_ifs with hi
  · rw [stL_getElem_wList]
    exact stL_wAt_wCat_lt h ha (by simpa [stL_length_wList] using hi)
  · rw [stL_getElem_wList, stL_length_wList]
    exact stL_wAt_wCat_ge h ha (by simpa [stL_length_wList] using hi)

theorem stL_wInH_wCat (h : wLen a + wLen b < 2 ^ 32) (ha : wInH a = true) (hb : wInH b = true) :
    wInH (wCat a b) = true := by
  refine (stL_wInH_iff _).2 ⟨stL_wOK_wCat h (stL_wOK_of_wInH ha) (stL_wOK_of_wInH hb),
    fun i hi => ?_⟩
  rw [stL_wLen_wCat h] at hi
  by_cases hia : i < wLen a
  · rw [stL_wAt_wCat_lt h (stL_wOK_of_wInH ha) hia]
    exact stL_wAt_lt_of_wInH ha i hia
  · rw [stL_wAt_wCat_ge h (stL_wOK_of_wInH ha) (by omega)]
    exact stL_wAt_lt_of_wInH hb _ (by omega)

end

private theorem build_spec (f : ℕ → ℕ) (hf : ∀ i, f i < 16) (n : ℕ) :
    (Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => acc ||| (f i <<< (4 * i))) n : ℕ) < 16 ^ n ∧
    ∀ j < n, (Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => acc ||| (f i <<< (4 * i))) n : ℕ) /
      16 ^ j % 16 = f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have e : (Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => acc ||| (f i <<< (4 * i))) (n + 1) : ℕ) =
        Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => acc ||| (f i <<< (4 * i))) n + 16 ^ n * f n := by
      show _ ||| (f n <<< (4 * n)) = _
      rw [stL_lor_shiftLeft (by rw [stL_two_pow_four_mul]; exact h1), stL_two_pow_four_mul]
    rw [e]
    refine ⟨stL_add_lt (l := 1) h1 (by simpa using hf n), fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [stL_digit_add_lt hj, h2 j hj]
    · rw [stL_digit_add_ge h1 le_rfl, Nat.sub_self, pow_zero, Nat.div_one,
        Nat.mod_eq_of_lt (hf _)]

private theorem rbuild_spec (f : ℕ → ℕ) (hf : ∀ i, f i < 16) (N : ℕ) : ∀ k ≤ N,
    ∃ Q < 16 ^ k, (∀ j < k, Q / 16 ^ j % 16 = f (k - 1 - j)) ∧
      (Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => acc ||| (f i <<< (4 * (N - 1 - i)))) k : ℕ) =
        16 ^ (N - k) * Q := by
  intro k
  induction k with
  | zero => intro _; exact ⟨0, by simp, fun j hj => absurd hj (Nat.not_lt_zero j), by simp⟩
  | succ k ih =>
    intro hk
    obtain ⟨Q, hQ, hQd, hR⟩ := ih (by omega)
    refine ⟨f k + 16 ^ 1 * Q, ?_, fun j hj => ?_, ?_⟩
    · have := stL_add_lt (k := 1) (l := k) (x := f k) (y := Q) (by simpa using hf k) hQ
      rwa [Nat.add_comm 1 k] at this
    · rcases j with _ | j
      · rw [show k + 1 - 1 - 0 = k by omega, stL_digit_add_lt (by norm_num : 0 < 1), pow_zero,
          Nat.div_one, Nat.mod_eq_of_lt (hf k)]
      · rw [stL_digit_add_ge (by simpa using hf k) (by omega), Nat.add_sub_cancel,
          hQd j (by omega), show k + 1 - 1 - (j + 1) = k - 1 - j by omega]
    · show (Nat.rec (motive := fun _ => ℕ) 0
          (fun i acc => acc ||| (f i <<< (4 * (N - 1 - i)))) k : ℕ) |||
          (f k <<< (4 * (N - 1 - k))) = _
      have hfk : f k <<< (4 * (N - 1 - k)) < 2 ^ (4 * (N - k)) := by
        rw [Nat.shiftLeft_eq, stL_two_pow_four_mul, stL_two_pow_four_mul,
          show N - k = (N - 1 - k) + 1 by omega, pow_succ, Nat.mul_comm (16 ^ _)]
        exact Nat.mul_lt_mul_of_pos_right (hf k) (by positivity)
      rw [hR, Nat.or_comm, show 16 ^ (N - k) * Q = Q <<< (4 * (N - k)) by
          rw [Nat.shiftLeft_eq, stL_two_pow_four_mul, Nat.mul_comm],
        stL_lor_shiftLeft hfk, Nat.shiftLeft_eq, stL_two_pow_four_mul, stL_two_pow_four_mul,
        show N - k = (N - (k + 1)) + 1 by omega, show N - 1 - k = N - (k + 1) by omega, pow_succ]
      ring

section
variable {w : ℕ}

private theorem wTh_eq (w : ℕ) : wTh w = wMk (wLen w) (Nat.rec (motive := fun _ => ℕ) 0
    (fun i acc => acc ||| (fld THM (4 * wAt w i) 15 <<< (4 * i))) (wLen w)) :=
  stL_sN _ _

theorem stL_wLen_wTh (w : ℕ) : wLen (wTh w) = wLen w := by
  rw [wTh_eq, stL_wLen_wMk _ (stL_wLen_lt w)]

theorem stL_wAt_wTh {i : ℕ} (hi : i < wLen w) : wAt (wTh w) i = fld THM (4 * wAt w i) 15 := by
  rw [wTh_eq, stL_wAt_eq, stL_wStr_wMk _ (stL_wLen_lt w)]
  exact (build_spec (fun i => fld THM (4 * wAt w i) 15) (fun _ => stL_thm_lt16 _) _).2 i hi

theorem stL_wOK_wTh (w : ℕ) : wOK (wTh w) = true := by
  rw [stL_wOK_iff, stL_wLen_wTh, wTh_eq, stL_wStr_wMk _ (stL_wLen_lt w)]
  exact (build_spec (fun i => fld THM (4 * wAt w i) 15) (fun _ => stL_thm_lt16 _) _).1

theorem stL_wList_wTh (w : ℕ) :
    wList (wTh w) = (wList w).map (fun c => fld THM (4 * c) 15) := by
  apply List.ext_getElem (by simp [stL_length_wList, stL_wLen_wTh])
  intro i h1 h2
  rw [stL_getElem_wList, List.getElem_map, stL_getElem_wList]
  exact stL_wAt_wTh (by simpa [stL_length_wList] using h2)

theorem stL_wInH_wTh (h : wInT w = true) : wInH (wTh w) = true := by
  refine (stL_wInH_iff _).2 ⟨stL_wOK_wTh w, fun i hi => ?_⟩
  rw [stL_wLen_wTh] at hi
  rw [stL_wAt_wTh hi]
  exact ((stL_wInT_iff w).1 h).2 i hi

end

section
variable {w : ℕ}

private theorem wRev_eq (w : ℕ) : wRev w = wMk (wLen w) (Nat.rec (motive := fun _ => ℕ) 0
    (fun i acc => acc ||| (wAt w i <<< (4 * (wLen w - 1 - i)))) (wLen w)) :=
  stL_sN _ _

private theorem wRev_str (w : ℕ) : ∃ Q < 16 ^ wLen w,
    (∀ j < wLen w, Q / 16 ^ j % 16 = wAt w (wLen w - 1 - j)) ∧ wStr (wRev w) = Q := by
  obtain ⟨Q, hQ, hQd, hR⟩ := rbuild_spec (wAt w) (stL_wAt_lt w) (wLen w) (wLen w) le_rfl
  refine ⟨Q, hQ, hQd, ?_⟩
  rw [wRev_eq, stL_wStr_wMk _ (stL_wLen_lt w), hR, Nat.sub_self, pow_zero, one_mul]

theorem stL_wLen_wRev (w : ℕ) : wLen (wRev w) = wLen w := by
  rw [wRev_eq, stL_wLen_wMk _ (stL_wLen_lt w)]

theorem stL_wAt_wRev {i : ℕ} (hi : i < wLen w) : wAt (wRev w) i = wAt w (wLen w - 1 - i) := by
  obtain ⟨Q, -, hQd, hS⟩ := wRev_str w
  rw [stL_wAt_eq, hS, hQd i hi]

theorem stL_wOK_wRev (w : ℕ) : wOK (wRev w) = true := by
  obtain ⟨Q, hQ, -, hS⟩ := wRev_str w
  rw [stL_wOK_iff, hS, stL_wLen_wRev]
  exact hQ

theorem stL_wList_wRev (w : ℕ) : wList (wRev w) = (wList w).reverse := by
  apply List.ext_getElem (by simp [stL_length_wList, stL_wLen_wRev])
  intro i h1 h2
  have hi : i < wLen w := by simpa [stL_length_wList] using h2
  rw [stL_getElem_wList, List.getElem_reverse, stL_getElem_wList, stL_length_wList,
    stL_wAt_wRev hi]

theorem stL_wInH_wRev (h : ∀ i < wLen w, wAt w i < 10) : wInH (wRev w) = true := by
  refine (stL_wInH_iff _).2 ⟨stL_wOK_wRev w, fun i hi => ?_⟩
  rw [stL_wLen_wRev] at hi
  rw [stL_wAt_wRev hi]
  exact h _ (by omega)

end

theorem stL_wLen_wOne (c : ℕ) : wLen (wOne c) = 1 := stL_wLen_wMk _ (by norm_num)

theorem stL_wAt_wOne {c : ℕ} (hc : c < 16) : wAt (wOne c) 0 = c := by
  rw [stL_wAt_eq, show wOne c = wMk 1 c from rfl, stL_wStr_wMk _ (by norm_num), pow_zero,
    Nat.div_one, Nat.mod_eq_of_lt hc]

theorem stL_wOK_wOne {c : ℕ} (hc : c < 16) : wOK (wOne c) = true := by
  rw [stL_wOK_iff, stL_wLen_wOne, show wOne c = wMk 1 c from rfl, stL_wStr_wMk _ (by norm_num)]
  simpa using hc

theorem stL_wList_wOne {c : ℕ} (hc : c < 16) : wList (wOne c) = [c] := by
  apply List.ext_getElem (by simp [stL_length_wList, stL_wLen_wOne])
  intro i h1 h2
  have hi : i = 0 := by simpa using h2
  subst hi
  rw [stL_getElem_wList, stL_wAt_wOne hc]
  rfl

theorem stL_wInH_wOne {c : ℕ} (hc : c < 10) : wInH (wOne c) = true := by
  refine (stL_wInH_iff _).2 ⟨stL_wOK_wOne (by omega), fun i hi => ?_⟩
  rw [stL_wLen_wOne] at hi
  obtain rfl : i = 0 := by omega
  rw [stL_wAt_wOne (by omega)]
  exact hc

private theorem hWord_eq (J : ℕ) :
    hWord J = wMk (J % 2 ^ 16) (J / 2 ^ 16 % 16 ^ (J % 2 ^ 16)) := by
  have e : J &&& 65535 = J % 2 ^ 16 := by
    rw [show (65535 : ℕ) = 2 ^ 16 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  show sN (J &&& 65535) (fun n => wMk n (fld J 16 ((1 <<< (4 * n)) - 1))) = _
  rw [stL_sN, e, Nat.one_shiftLeft, stL_fld_eq, stL_two_pow_four_mul]

theorem stL_wLen_hWord (J : ℕ) : wLen (hWord J) < 2 ^ 16 := by
  have h : J % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (by positivity)
  rw [hWord_eq, stL_wLen_wMk _ (by omega)]
  exact h

theorem stL_wOK_hWord (J : ℕ) : wOK (hWord J) = true := by
  have h : J % 2 ^ 16 < 2 ^ 32 := lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (by norm_num)
  rw [stL_wOK_iff, hWord_eq, stL_wStr_wMk _ h, stL_wLen_wMk _ h]
  exact Nat.mod_lt _ (by positivity)

section
variable {G : Type*} [Group G]

theorem stL_evalWord_append (g : ℕ → G) (l₁ l₂ : List ℕ) :
    evalWord g (l₁ ++ l₂) = evalWord g l₁ * evalWord g l₂ := by
  simp [evalWord, List.map_append, List.prod_append]

theorem stL_evalWord_reverse {g : ℕ → G} (hg : ∀ c, g c * g c = 1) (l : List ℕ) :
    evalWord g l.reverse = (evalWord g l)⁻¹ := by
  induction l with
  | nil => simp [evalWord]
  | cons c l ih =>
    have h1 : evalWord g [c] = g c := by simp [evalWord]
    rw [List.reverse_cons, stL_evalWord_append, ih, h1, evalWord_cons, mul_inv_rev,
      inv_eq_of_mul_eq_one_right (hg c)]

theorem stL_evalWord_thm {x : ℕ → G} {u : G} (hu : u * u = 1)
    (hθ : ∀ c < 10, c ≠ 7 → u * x c * u = x (fld THM (4 * c) 15)) (l : List ℕ)
    (hl : ∀ c ∈ l, c < 10 ∧ c ≠ 7) :
    evalWord x (l.map fun c => fld THM (4 * c) 15) = u * evalWord x l * u := by
  induction l with
  | nil => simp [evalWord, hu]
  | cons c l ih =>
    have hc := hl c (by simp)
    rw [List.map_cons, evalWord_cons, evalWord_cons, ih fun d hd => hl d (by simp [hd]),
      ← hθ c hc.1 hc.2]
    calc u * x c * u * (u * evalWord x l * u) = u * x c * (u * u) * evalWord x l * u := by group
      _ = u * (x c * evalWord x l) * u := by rw [hu]; group

theorem stL_val_wCat (g : ℕ → G) {a b : ℕ} (h : wLen a + wLen b < 2 ^ 32) (ha : wOK a = true) :
    evalWord g (wList (wCat a b)) = evalWord g (wList a) * evalWord g (wList b) := by
  rw [stL_wList_wCat h ha, stL_evalWord_append]

theorem stL_val_wRev {g : ℕ → G} (hg : ∀ c, g c * g c = 1) (w : ℕ) :
    evalWord g (wList (wRev w)) = (evalWord g (wList w))⁻¹ := by
  rw [stL_wList_wRev, stL_evalWord_reverse hg]

theorem stL_val_wTh {x : ℕ → G} {u : G} (hu : u * u = 1)
    (hθ : ∀ c < 10, c ≠ 7 → u * x c * u = x (fld THM (4 * c) 15)) {w : ℕ} (h : wInT w = true) :
    evalWord x (wList (wTh w)) = u * evalWord x (wList w) * u := by
  rw [stL_wList_wTh]
  refine stL_evalWord_thm hu hθ _ fun c hc => ?_
  obtain ⟨i, hi, rfl⟩ := stL_mem_wList.1 hc
  exact stL_thm_lt (stL_wAt_lt w i) (((stL_wInT_iff w).1 h).2 i hi)

theorem stL_val_wOne (g : ℕ → G) {c : ℕ} (hc : c < 16) : evalWord g (wList (wOne c)) = g c := by
  rw [stL_wList_wOne hc]
  simp [evalWord]

theorem stL_val_zero (g : ℕ → G) : evalWord g (wList 0) = 1 := by
  rw [stL_wList_zero]; rfl

end

end CFSG.KC.B433Alt

end
