module

public import Certificates.Data.Kernel.B3MK
public import CFSG.Certificates.Kernel.WEMKSound

set_option exponentiation.threshold 1024

public section

namespace CFSG.StandardType.ZS.B3MK

open Certificates.ExcModel Certificates.WEMK Certificates.B3MK CFSG.StandardType.ZS CFSG.StandardType.ZS.WEMK

@[expose] def ln (x l : ℕ) : ℕ := x / 2 ^ (32 * l) % 2 ^ 32

@[expose] def decW (x : ℕ) : Mat 4 := Matrix.of fun i j => ((ln x (4 * i.val + j.val) : ℕ) : ZMod 13)

@[expose] def pkF : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => pkF n f + 2 ^ (32 * n) * f n

theorem ln_lt (x l : ℕ) : ln x l < 2 ^ 32 := Nat.mod_lt _ (by positivity)

theorem ln_zero (l : ℕ) : ln 0 l = 0 := by simp [ln]

theorem ln_add_mul_pow {A B n j : ℕ} (hj : j < n) : ln (A + 2 ^ (32 * n) * B) j = ln A j := by
  obtain ⟨k, rfl⟩ : ∃ k, n = j + 1 + k := ⟨n - (j + 1), by omega⟩
  have h : 2 ^ (32 * (j + 1 + k)) * B = 2 ^ (32 * j) * (2 ^ 32 * (2 ^ (32 * k) * B)) := by
    rw [show 32 * (j + 1 + k) = 32 * j + 32 + 32 * k by ring, pow_add, pow_add]
    ring
  rw [ln, ln, h, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

theorem ln_add_mul_pow_self {A B n : ℕ} (hA : A < 2 ^ (32 * n)) : ln (A + 2 ^ (32 * n) * B) n = B % 2 ^ 32 := by
  rw [ln, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hA, zero_add]

theorem pkF_lt {n : ℕ} {f : ℕ → ℕ} (hf : ∀ j < n, f j < 2 ^ 32) : pkF n f < 2 ^ (32 * n) := by
  induction n with
  | zero => simp [pkF]
  | succ n ih =>
    rw [pkF]
    have h1 := ih fun j hj => hf j (by omega)
    have h2 := hf n (by omega)
    have h3 : 2 ^ (32 * (n + 1)) = 2 ^ (32 * n) * 2 ^ 32 := by rw [show 32 * (n + 1) = 32 * n + 32 by ring, pow_add]
    rw [h3]
    nlinarith

theorem ln_pkF {n : ℕ} {f : ℕ → ℕ} (hf : ∀ j < n, f j < 2 ^ 32) {j : ℕ} (hj : j < n) : ln (pkF n f) j = f j := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [pkF]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [ln_add_mul_pow hj]
      exact ih (fun k hk => hf k (by omega)) hj
    · rw [ln_add_mul_pow_self (pkF_lt fun k hk => hf k (by omega))]
      exact Nat.mod_eq_of_lt (hf j (by omega))

theorem pkF_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, f j = g j) : pkF n f = pkF n g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pkF, pkF, ih fun j hj => h j (by omega), h n (by omega)]

theorem pkF_add (n : ℕ) (f g : ℕ → ℕ) : pkF n f + pkF n g = pkF n fun l => f l + g l := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pkF, pkF, pkF, ← ih]; ring

theorem pkF_mul (n c : ℕ) (f : ℕ → ℕ) : c * pkF n f = pkF n fun l => c * f l := by
  induction n with
  | zero => simp [pkF]
  | succ n ih => rw [pkF, pkF, ← ih]; ring

theorem pkF_zero (n : ℕ) : pkF n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pkF, ih]; simp

theorem eq_pkF_ln {n x : ℕ} (hx : x < 2 ^ (32 * n)) : x = pkF n (ln x) := by
  induction n generalizing x with
  | zero => simp at hx; simp [hx, pkF]
  | succ n ih =>
    have hB : 2 ^ (32 * (n + 1)) = 2 ^ (32 * n) * 2 ^ 32 := by rw [show 32 * (n + 1) = 32 * n + 32 by ring, pow_add]
    have hpos : 0 < 2 ^ (32 * n) := by positivity
    have hlo := Nat.mod_lt x hpos
    have hdiv : x / 2 ^ (32 * n) < 2 ^ 32 := by
      rw [Nat.div_lt_iff_lt_mul hpos]
      rw [hB] at hx
      linarith
    have hsplit : x = x % 2 ^ (32 * n) + 2 ^ (32 * n) * (x / 2 ^ (32 * n)) := (Nat.mod_add_div x _).symm
    rw [pkF]
    have hl : ∀ j < n, ln (x % 2 ^ (32 * n)) j = ln x j := fun j hj => by
      conv_rhs => rw [hsplit]
      rw [ln_add_mul_pow hj]
    have htop : ln x n = x / 2 ^ (32 * n) := by
      conv_lhs => rw [hsplit]
      rw [ln_add_mul_pow_self hlo, Nat.mod_eq_of_lt hdiv]
    rw [← pkF_congr hl, ← ih hlo, htop]
    exact hsplit

theorem eq_zero_of_ln {n x : ℕ} (hx : x < 2 ^ (32 * n)) (h : ∀ l < n, ln x l = 0) : x = 0 := by
  rw [eq_pkF_ln hx, pkF_congr h, pkF_zero]

theorem ln_and (x y l : ℕ) : ln (x &&& y) l = ln x l &&& ln y l := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [ln, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_and]
  cases decide (i < 32) <;> simp

theorem ln_shr (x m l : ℕ) : ln (x >>> (32 * m)) l = ln x (l + m) := by
  rw [ln, ln, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add]
  congr 3
  ring

theorem ln_mod {y n l : ℕ} (hl : l < n) : ln (y % 2 ^ (32 * n)) l = ln y l := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [ln, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < 32
  · have : i + 32 * l < 32 * n := by omega
    simp [hi, this]
  · simp [hi]

theorem and_full {v : ℕ} (hv : v < 2 ^ 32) : v &&& 4294967295 = v := by
  rw [show (4294967295 : ℕ) = 2 ^ 32 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hv]

theorem mE_lt : mHi < 2 ^ (32 * 16) ∧ m3 < 2 ^ (32 * 16) ∧ mB4 < 2 ^ (32 * 16) ∧ mCol < 2 ^ (32 * 16) ∧
    mL16 < 2 ^ (32 * 16) ∧ idW < 2 ^ (32 * 16) := by
  decide +kernel

theorem ln_masks : ∀ l < 16, ln mHi l = 4294967280 ∧ ln m3 l = 3 ∧ ln mB4 l = 16 ∧
    ln mCol l = (if l % 4 = 0 then 4294967295 else 0) ∧ ln mL16 l = 65535 ∧ ln idW l = (if l % 5 = 0 then 1 else 0) := by
  decide +kernel

theorem mRow_eq : mRow = 2 ^ 128 - 1 := by decide +kernel

theorem lt16_of_and {v : ℕ} (hv : v < 2 ^ 32) (h : v &&& 4294967280 = 0) : v < 16 := by
  apply Nat.lt_pow_two_of_testBit (n := 4)
  intro i hi
  by_cases h32 : i < 32
  · have hm : ∀ i < 32, 4 ≤ i → Nat.testBit 4294967280 i = true := by decide +kernel
    have := congrArg (Nat.testBit · i) h
    simp only [Nat.testBit_and, hm i h32 hi, Bool.and_true, Nat.zero_testBit] at this
    exact this
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem lane_facts : (∀ v < 13, v &&& 4294967280 = 0 ∧ (v + 3) &&& 16 = 0) ∧
    (∀ v < 16, (v + 3) &&& 16 = 0 → v < 13) := by
  decide +kernel

theorem wfW_eq (x : ℕ) : wfW x = (Nat.beq (x >>> 512) 0 && Nat.beq (x &&& mHi) 0 && Nat.beq ((x + m3) &&& mB4) 0) :=
  rfl

theorem wfW_iff (x : ℕ) : wfW x = true ↔ x < 2 ^ (32 * 16) ∧ ∀ l < 16, ln x l < 13 := by
  obtain ⟨hHi, h3, hB4, -, -, -⟩ := mE_lt
  have hsum : ∀ y, y < 2 ^ (32 * 16) → (∀ l < 16, ln y l < 16) → ∀ l < 16, ln (y + m3) l = ln y l + 3 := by
    intro y hy hl l hl16
    have hb : ∀ j < 16, ln y j + ln m3 j < 2 ^ 32 := fun j hj => by
      have := hl j hj
      rw [(ln_masks j hj).2.1]
      omega
    have e : y + m3 = pkF 16 fun j => ln y j + ln m3 j := by
      conv_lhs => rw [eq_pkF_ln hy, eq_pkF_ln h3]
      rw [pkF_add]
    rw [e, ln_pkF hb hl16, (ln_masks l hl16).2.1]
  rw [wfW_eq]
  simp only [Bool.and_eq_true, Nat.beq_eq]
  constructor
  · rintro ⟨⟨hs, hh⟩, hb⟩
    have hx : x < 2 ^ (32 * 16) := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] at hs
      omega
    have h16 : ∀ l < 16, ln x l < 16 := fun l hl => by
      have := congrArg (ln · l) hh
      simp only [ln_and, ln_zero, (ln_masks l hl).1] at this
      exact lt16_of_and (ln_lt x l) this
    refine ⟨hx, fun l hl => lane_facts.2 _ (h16 l hl) ?_⟩
    have := congrArg (ln · l) hb
    simp only [ln_and, ln_zero, (ln_masks l hl).2.2.1, hsum x hx h16 l hl] at this
    exact this
  · rintro ⟨hx, hl⟩
    have h16 : ∀ l < 16, ln x l < 16 := fun l h => by have := hl l h; omega
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hx]
    · refine eq_zero_of_ln (Nat.and_lt_two_pow _ hHi) fun l h => ?_
      rw [ln_and, (ln_masks l h).1]
      exact (lane_facts.1 _ (hl l h)).1
    · refine eq_zero_of_ln (Nat.and_lt_two_pow _ hB4) fun l h => ?_
      rw [ln_and, (ln_masks l h).2.2.1, hsum x hx h16 l h]
      exact (lane_facts.1 _ (hl l h)).2

theorem wf_pkF {f : ℕ → ℕ} (hf : ∀ l < 16, f l < 13) : wfW (pkF 16 f) = true := by
  have hf' : ∀ l < 16, f l < 2 ^ 32 := fun l h => by have := hf l h; omega
  rw [wfW_iff]
  exact ⟨pkF_lt hf', fun l h => by rw [ln_pkF hf' h]; exact hf l h⟩

theorem decW_pkF {f : ℕ → ℕ} (hf : ∀ l < 16, f l < 13) (i j : Fin 4) :
    decW (pkF 16 f) i j = ((f (4 * i.val + j.val) : ℕ) : ZMod 13) := by
  have hf' : ∀ l < 16, f l < 2 ^ 32 := fun l h => by have := hf l h; omega
  simp only [decW, Matrix.of_apply]
  rw [ln_pkF hf' (by omega)]

theorem decW_idW : decW idW = 1 := by
  have h := mE_lt.2.2.2.2.2
  ext i j
  simp only [decW, Matrix.of_apply, (ln_masks _ (by omega : 4 * i.val + j.val < 16)).2.2.2.2.2, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    have : (4 * i.val + i.val) % 5 = 0 := by omega
    simp [this]
  · have : (4 * i.val + j.val) % 5 ≠ 0 := by
      intro h'
      apply hij
      ext
      omega
    simp [this, hij]

theorem wfW_idW : wfW idW = true := by
  rw [wfW_iff]
  refine ⟨mE_lt.2.2.2.2.2, fun l hl => ?_⟩
  rw [(ln_masks l hl).2.2.2.2.2]
  split <;> omega

theorem wfW_inj {x y : ℕ} (hx : wfW x = true) (hy : wfW y = true) (h : decW x = decW y) : x = y := by
  rw [wfW_iff] at hx hy
  rw [eq_pkF_ln hx.1, eq_pkF_ln hy.1]
  refine pkF_congr fun l hl => ?_
  have e := congrFun (congrFun h ⟨l / 4, by omega⟩) ⟨l % 4, by omega⟩
  simp only [decW, Matrix.of_apply] at e
  rw [show 4 * (l / 4) + l % 4 = l by omega] at e
  have := congrArg ZMod.val e
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (hx.2 l hl), Nat.mod_eq_of_lt (hy.2 l hl)] at this

theorem lmul_eq (g x : ℕ) : lmul g x = red ((g >>> (32 * 0) &&& mCol) * (x >>> (32 * (4 * 0)) &&& mRow) +
    (g >>> (32 * 1) &&& mCol) * (x >>> (32 * (4 * 1)) &&& mRow) +
    ((g >>> (32 * 2) &&& mCol) * (x >>> (32 * (4 * 2)) &&& mRow) + (g >>> (32 * 3) &&& mCol) * (x >>> (32 * (4 * 3))))) :=
  rfl

theorem red_eq (P : ℕ) : red P = P - 13 * ((P * 5042) >>> 16 &&& mL16) := rfl

theorem colA {g : ℕ} (k : ℕ) : g >>> (32 * k) &&& mCol = pkF 16 fun l => if l % 4 = 0 then ln g (l + k) else 0 := by
  rw [eq_pkF_ln (Nat.and_lt_two_pow _ mE_lt.2.2.2.1)]
  refine pkF_congr fun l hl => ?_
  rw [ln_and, ln_shr, (ln_masks l hl).2.2.2.1]
  split
  · exact and_full (ln_lt _ _)
  · simp

theorem rowB {x : ℕ} (k : ℕ) : x >>> (32 * (4 * k)) &&& mRow = pkF 4 fun l => ln x (l + 4 * k) := by
  rw [mRow_eq, Nat.and_two_pow_sub_one_eq_mod, show 128 = 32 * 4 by rfl, eq_pkF_ln (Nat.mod_lt _ (by positivity))]
  exact pkF_congr fun l hl => by rw [ln_mod hl, ln_shr]

theorem rowB3 {x : ℕ} (hx : x < 2 ^ (32 * 16)) : x >>> (32 * (4 * 3)) = pkF 4 fun l => ln x (l + 4 * 3) := by
  have h : x >>> (32 * (4 * 3)) < 2 ^ (32 * 4) := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    exact hx
  rw [eq_pkF_ln h]
  exact pkF_congr fun l _ => ln_shr _ _ _

theorem mul_col_row (a b : ℕ → ℕ) : (pkF 16 fun l => if l % 4 = 0 then a l else 0) * pkF 4 b =
    pkF 16 fun l => a (4 * (l / 4)) * b (l % 4) := by
  simp only [pkF]
  norm_num
  ring

theorem red_lanes {s : ℕ → ℕ} (hs : ∀ l < 16, s l < 577) : red (pkF 16 s) = pkF 16 fun l => s l % 13 := by
  have hd : ∀ v < 577, 13 * (5042 * v / 65536) ≤ v ∧ v - 13 * (5042 * v / 65536) = v % 13 := by decide +kernel
  have hy : ∀ l < 16, 5042 * s l < 2 ^ 32 := fun l h => by have := hs l h; omega
  have hq : (pkF 16 s * 5042) >>> 16 &&& mL16 = pkF 16 fun l => 5042 * s l / 65536 := by
    rw [eq_pkF_ln (Nat.and_lt_two_pow _ mE_lt.2.2.2.2.1)]
    refine pkF_congr fun l hl => ?_
    rw [ln_and, (ln_masks l hl).2.2.2.2.1, show (65535 : ℕ) = 2 ^ 16 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
      mul_comm, pkF_mul]
    have e := ln_pkF hy hl
    rw [ln, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, Nat.mod_mod_of_dvd _ (by norm_num)] at *
    rw [← e, mul_comm (2 ^ 16), ← Nat.div_div_eq_div_mul, ← Nat.mod_mul_right_div_self, show 2 ^ 16 * 2 ^ 16 = 2 ^ 32 by
      norm_num]
  rw [red_eq, hq, pkF_mul]
  have hsplit : pkF 16 s = (pkF 16 fun l => s l % 13) + pkF 16 fun l => 13 * (5042 * s l / 65536) := by
    rw [pkF_add]
    refine pkF_congr fun l hl => ?_
    have := hd _ (hs l hl)
    omega
  omega

theorem lmul_spec {g x : ℕ} (hg : wfW g = true) (hx : wfW x = true) :
    wfW (lmul g x) = true ∧ decW (lmul g x) = decW g * decW x := by
  rw [wfW_iff] at hg hx
  set G := ln g
  set X := ln x
  set t : ℕ → ℕ → ℕ := fun k l => G (4 * (l / 4) + k) * X (l % 4 + 4 * k)
  have ht : ∀ k, (g >>> (32 * k) &&& mCol) * (x >>> (32 * (4 * k)) &&& mRow) = pkF 16 (t k) := fun k => by
    rw [colA, rowB, mul_col_row]
  have ht3 : (g >>> (32 * 3) &&& mCol) * (x >>> (32 * (4 * 3))) = pkF 16 (t 3) := by
    rw [colA, rowB3 hx.1, mul_col_row]
  have hGX : ∀ k < 4, ∀ l < 16, t k l ≤ 144 := fun k hk l hl => by
    have h1 := hg.2 (4 * (l / 4) + k) (by omega)
    have h2 := hx.2 (l % 4 + 4 * k) (by omega)
    exact Nat.mul_le_mul (Nat.le_of_lt_succ h1) (Nat.le_of_lt_succ h2)
  set s : ℕ → ℕ := fun l => t 0 l + t 1 l + (t 2 l + t 3 l)
  have hs : ∀ l < 16, s l < 577 := fun l hl => by
    have := hGX 0 (by omega) l hl
    have := hGX 1 (by omega) l hl
    have := hGX 2 (by omega) l hl
    have := hGX 3 (by omega) l hl
    simp only [s]
    omega
  have hm : lmul g x = pkF 16 fun l => s l % 13 := by
    rw [lmul_eq, ht 0, ht 1, ht 2, ht3, pkF_add, pkF_add, pkF_add, red_lanes hs]
  have h13 : ∀ l < 16, s l % 13 < 13 := fun _ _ => Nat.mod_lt _ (by norm_num)
  refine ⟨hm ▸ wf_pkF h13, ?_⟩
  rw [hm]
  ext i j
  rw [decW_pkF h13, Matrix.mul_apply, Fin.sum_univ_four]
  have hi : (4 * i.val + j.val) / 4 = i.val := by omega
  have hj : (4 * i.val + j.val) % 4 = j.val := by omega
  simp only [s, t, hi, hj, decW, Matrix.of_apply, ZMod.natCast_mod, G, X]
  push_cast
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show ((3 : Fin 4) : ℕ) = 3 from rfl]
  ring_nf

theorem pkF_eq_sum (n : ℕ) (f : ℕ → ℕ) : pkF n f = ∑ l ∈ Finset.range n, (2 ^ 32) ^ l * f l := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pkF, ih, Finset.sum_range_succ, pow_mul]

theorem toW_B (A : NMat) : toW A = ((List.range 4).flatMap fun i => (List.range 4).map fun j =>
    ((A.getD i []).getD j 0) * (2 ^ 32) ^ (4 * i + j)).sum := by
  unfold toW
  congr
  funext i
  congr
  funext j
  rw [pow_mul]

theorem sum16 (F : ℕ → ℕ → ℕ) (B : ℕ) : (([0, 1, 2, 3] : List ℕ).flatMap fun i =>
    ([0, 1, 2, 3] : List ℕ).map fun j => F i j * B ^ (4 * i + j)).sum =
      ∑ l ∈ Finset.range 16, B ^ l * F (l / 4) (l % 4) := by
  simp only [List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.nil_append, List.cons_append,
    List.sum_cons, List.sum_nil, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

theorem range4 : List.range 4 = [0, 1, 2, 3] := rfl

theorem toW_eq (A : NMat) : toW A = pkF 16 fun l => (A.getD (l / 4) []).getD (l % 4) 0 := by
  rw [toW_B, range4, sum16 (fun i j => (A.getD i []).getD j 0), pkF_eq_sum]

theorem decW_toW {A : NMat} (hA : ∀ r ∈ A, ∀ x ∈ r, x < 13) : wfW (toW A) = true ∧ decW (toW A) = toM 4 A := by
  set f : ℕ → ℕ := fun l => (A.getD (l / 4) []).getD (l % 4) 0
  have hf : ∀ l, f l < 13 := fun l => by
    have hr := getD_prop (fun r : List ℕ => ∀ x ∈ r, x < 13) A [] (l / 4) hA (by simp)
    exact getD_prop (fun x : ℕ => x < 13) _ 0 (l % 4) hr (by norm_num)
  rw [toW_eq A]
  refine ⟨wf_pkF fun l _ => hf l, ?_⟩
  ext i j
  rw [decW_pkF (fun l _ => hf l), toM_apply]
  have hi : (4 * i.val + j.val) / 4 = i.val := by omega
  have hj : (4 * i.val + j.val) % 4 = j.val := by omega
  simp only [f, hi, hj]

theorem mat_lt (q : KPair) : ∀ r ∈ mat 4 q, ∀ x ∈ r, x < 13 := by
  intro r hr x hx
  simp only [mat, List.mem_map, List.mem_range] at hr
  obtain ⟨i, -, rfl⟩ := hr
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨j, -, rfl⟩ := hx
  exact Nat.mod_lt _ (by norm_num)

theorem decW_toW_mat (q : KPair) : wfW (toW (mat 4 q)) = true ∧ decW (toW (mat 4 q)) = toM 4 (mat 4 q) :=
  decW_toW (mat_lt q)

theorem o2q_of {q : ℕ} (hq : wfW q = true) (h1 : decW q ≠ 1) (h2 : decW q ^ 2 = 1) : o2q q = true := by
  simp only [o2q, Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq]
  refine ⟨?_, ?_⟩
  · cases hb : Nat.beq q idW
    · rfl
    · rw [Nat.beq_eq] at hb
      exact absurd (hb ▸ decW_idW) h1
  · obtain ⟨hw, hd⟩ := lmul_spec hq hq
    refine wfW_inj hw wfW_idW ?_
    rw [hd, decW_idW, ← sq, h2]

theorem o2W_of {a b : ℕ} (ha : wfW a = true) (hb : wfW b = true) (h1 : decW a * decW b ≠ 1)
    (h2 : (decW a * decW b) ^ 2 = 1) : o2W a b = true := by
  obtain ⟨hw, hd⟩ := lmul_spec ha hb
  exact o2q_of hw (hd ▸ h1) (hd ▸ h2)

theorem o4W_of {a b : ℕ} (ha : wfW a = true) (hb : wfW b = true) (h1 : (decW a * decW b) ^ 2 ≠ 1)
    (h2 : (decW a * decW b) ^ 4 = 1) : o4W a b = true := by
  obtain ⟨hw, hd⟩ := lmul_spec ha hb
  obtain ⟨hw2, hd2⟩ := lmul_spec hw hw
  refine o2q_of hw2 ?_ ?_
  · rw [hd2, ← sq, hd]
    exact h1
  · rw [hd2, ← sq, hd, ← pow_mul]
    exact h2

theorem pick4_mem (a b c d l : ℕ) : pick4 a b c d l = a ∨ pick4 a b c d l = b ∨ pick4 a b c d l = c ∨
    pick4 a b c d l = d := by
  unfold pick4
  cases Nat.beq l 0 <;> cases Nat.beq l 1 <;> cases Nat.beq l 2 <;> simp

theorem evalW_spec (a b c d : ℕ) (w : List ℕ) (X : ℕ) (h : ∀ y ∈ [a, b, c, d, X], wfW y = true) :
    wfW (evalW a b c d w X) = true ∧
      decW (evalW a b c d w X) = (w.map fun l => decW (pick4 a b c d l)).reverse.prod * decW X := by
  induction w generalizing X with
  | nil => exact ⟨h X (by simp), by simp [evalW]⟩
  | cons l w ih =>
    have hp : wfW (pick4 a b c d l) = true := by
      rcases pick4_mem a b c d l with e | e | e | e <;> rw [e] <;> exact h _ (by simp)
    obtain ⟨hw, hd⟩ := lmul_spec hp (h X (by simp))
    have hrest : ∀ y ∈ [a, b, c, d, lmul (pick4 a b c d l) X], wfW y = true := by
      intro y hy
      rcases List.mem_cons.mp hy with e | hy
      · exact e ▸ h a (by simp)
      rcases List.mem_cons.mp hy with e | hy
      · exact e ▸ h b (by simp)
      rcases List.mem_cons.mp hy with e | hy
      · exact e ▸ h c (by simp)
      rcases List.mem_cons.mp hy with e | hy
      · exact e ▸ h d (by simp)
      rw [List.mem_singleton] at hy
      exact hy ▸ hw
    obtain ⟨ih1, ih2⟩ := ih _ hrest
    refine ⟨ih1, ?_⟩
    change decW (evalW a b c d w (lmul (pick4 a b c d l) X)) = _
    rw [ih2, hd, List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton, mul_assoc]

theorem beq_false_iff (a b : ℕ) : Nat.beq a b = false ↔ a ≠ b := by
  rw [Bool.eq_false_iff, Ne, Ne, Nat.beq_eq]

theorem lenL_eq {α : Type} (l : List α) : lenL l = l.length := by
  induction l with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem memN_iff (j : ℕ) (J : List ℕ) : memN j J = true ↔ j ∈ J := by
  induction J with
  | nil => simp [memN]
  | cons a J ih =>
    change (Nat.beq a j || memN j J) = true ↔ _
    rw [Bool.or_eq_true, Nat.beq_eq, ih, List.mem_cons]
    exact ⟨fun h => h.imp_left Eq.symm, fun h => h.imp_left Eq.symm⟩

theorem notIn_iff (x : ℕ) (H : List ℕ) : notIn x H = true ↔ x ∉ H := by
  induction H with
  | nil => simp [notIn]
  | cons h H ih =>
    change (!(Nat.beq h x) && notIn x H) = true ↔ _
    rw [Bool.and_eq_true, Bool.not_eq_true', beq_false_iff, ih, List.mem_cons, not_or]
    exact ⟨fun e => ⟨Ne.symm e.1, e.2⟩, fun e => ⟨Ne.symm e.1, e.2⟩⟩

def chainsAux (r0 r2 : ℕ) (J VW : List ℕ) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun x _ ih j => (!(o2W r0 x && o4W r2 x) || memN j J) && ih (Nat.succ j)) VW

theorem chainsAux_sound (r0 r2 : ℕ) (J : List ℕ) : ∀ (VW : List ℕ) (j0 : ℕ), chainsAux r0 r2 J VW j0 = true →
    ∀ j < VW.length, o2W r0 (VW.getD j 0) = true → o4W r2 (VW.getD j 0) = true → j0 + j ∈ J
  | [], _, _, j, hj => by simp at hj
  | x :: VW, j0, h, j, hj => by
    change ((!(o2W r0 x && o4W r2 x) || memN j0 J) && chainsAux r0 r2 J VW (j0 + 1)) = true at h
    rw [Bool.and_eq_true] at h
    intro h2 h4
    cases j with
    | zero =>
      rw [List.getD_cons_zero] at h2 h4
      rw [h2, h4] at h
      simpa [memN_iff] using h.1
    | succ j =>
      rw [List.getD_cons_succ] at h2 h4
      have := chainsAux_sound r0 r2 J VW (j0 + 1) h.2 j (by simpa using hj) h2 h4
      rwa [show j0 + 1 + j = j0 + (j + 1) by omega] at this

theorem chainsOK_sound {r0 r2 : ℕ} {J VW : List ℕ} (h : chainsOK r0 r2 J VW = true) :
    ∀ j < VW.length, o2W r0 (VW.getD j 0) = true → o4W r2 (VW.getD j 0) = true → j ∈ J := fun j hj h2 h4 => by
  simpa using chainsAux_sound r0 r2 J VW 0 h j hj h2 h4

def closeAux (Ep Tp n x k : ℕ) (gs : List ℕ) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun g _ ih c => stepOK Ep n g x (get9 Tp (Nat.add (Nat.mul 4 k) c)) && ih (Nat.succ c)) gs

theorem closeAux_sound (Ep Tp n x k : ℕ) : ∀ (gs : List ℕ) (c0 : ℕ), closeAux Ep Tp n x k gs c0 = true →
    ∀ c < gs.length, get9 Tp (4 * k + (c0 + c)) < n ∧ lmul (gs.getD c 0) x = getE Ep (get9 Tp (4 * k + (c0 + c)))
  | [], _, _, c, hc => by simp at hc
  | g :: gs, c0, h, c, hc => by
    change (stepOK Ep n g x (get9 Tp (4 * k + c0)) && closeAux Ep Tp n x k gs (c0 + 1)) = true at h
    rw [Bool.and_eq_true] at h
    cases c with
    | zero =>
      have h1 := h.1
      simp only [stepOK, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h1
      simpa using h1
    | succ c =>
      have := closeAux_sound Ep Tp n x k gs (c0 + 1) h.2 c (by simpa using hc)
      rw [List.getD_cons_succ]
      rwa [show c0 + 1 + c = c0 + (c + 1) by omega] at this

def elemsAux (Ep Tp n : ℕ) (gs E : List ℕ) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun x _ ih k => (wfW x && Nat.beq (getE Ep k) x && closeG Ep Tp n x k gs) && ih (Nat.succ k)) E

theorem elemsAux_sound (Ep Tp n : ℕ) (gs : List ℕ) : ∀ (E : List ℕ) (k0 : ℕ), elemsAux Ep Tp n gs E k0 = true →
    (∀ x ∈ E, wfW x = true) ∧ ∀ k < E.length, getE Ep (k0 + k) = E.getD k 0 ∧ ∀ c < gs.length,
      get9 Tp (4 * (k0 + k) + c) < n ∧ lmul (gs.getD c 0) (E.getD k 0) = getE Ep (get9 Tp (4 * (k0 + k) + c))
  | [], _, _ => ⟨by simp, fun k hk => by simp at hk⟩
  | x :: E, k0, h => by
    change ((wfW x && Nat.beq (getE Ep k0) x && closeAux Ep Tp n x k0 gs 0) &&
      elemsAux Ep Tp n gs E (k0 + 1)) = true at h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨⟨⟨hw, he⟩, hc⟩, hr⟩ := h
    obtain ⟨ih1, ih2⟩ := elemsAux_sound Ep Tp n gs E (k0 + 1) hr
    refine ⟨fun y hy => ?_, fun k hk => ?_⟩
    · rcases List.mem_cons.mp hy with e | hy
      · exact e ▸ hw
      · exact ih1 y hy
    · cases k with
      | zero =>
        refine ⟨by simpa using he, fun c hc' => ?_⟩
        simpa using closeAux_sound Ep Tp n x k0 gs 0 hc c hc'
      | succ k =>
        obtain ⟨e1, e2⟩ := ih2 k (by simpa using hk)
        rw [show k0 + (k + 1) = k0 + 1 + k by omega, List.getD_cons_succ]
        exact ⟨e1, e2⟩

theorem elemsOK_sound {Ep Tp n : ℕ} {gs E : List ℕ} (h : elemsOK Ep Tp n gs E = true) :
    (∀ x ∈ E, wfW x = true) ∧ ∀ k < E.length, getE Ep k = E.getD k 0 ∧ ∀ c < gs.length,
      get9 Tp (4 * k + c) < n ∧ lmul (gs.getD c 0) (E.getD k 0) = getE Ep (get9 Tp (4 * k + c)) := by
  simpa using elemsAux_sound Ep Tp n gs E 0 h

def treeAux (Tp Dp n i0 : ℕ) (par : List (ℕ × ℕ)) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun pc _ ih k => treeRow Tp Dp n i0 k pc && ih (Nat.succ k)) par

theorem treeAux_sound (Tp Dp n i0 : ℕ) : ∀ (par : List (ℕ × ℕ)) (k0 : ℕ), treeAux Tp Dp n i0 par k0 = true →
    ∀ k < par.length, (k0 + k = i0 ∧ get9 Dp (k0 + k) = 0) ∨ ((par.getD k (0, 0)).1 < n ∧ (par.getD k (0, 0)).2 < 4 ∧
      get9 Tp (4 * (par.getD k (0, 0)).1 + (par.getD k (0, 0)).2) = k0 + k ∧
      get9 Dp (k0 + k) = get9 Dp (par.getD k (0, 0)).1 + 1)
  | [], _, _, k, hk => by simp at hk
  | pc :: par, k0, h, k, hk => by
    change (treeRow Tp Dp n i0 k0 pc && treeAux Tp Dp n i0 par (k0 + 1)) = true at h
    rw [Bool.and_eq_true] at h
    cases k with
    | zero =>
      have h1 := h.1
      simp only [treeRow, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h1
      simp only [List.getD_cons_zero, Nat.add_zero]
      rcases h1 with ⟨a, b⟩ | ⟨⟨⟨a, b⟩, c⟩, d⟩
      · exact Or.inl ⟨a, b⟩
      · exact Or.inr ⟨a, b, c, d⟩
    | succ k =>
      have := treeAux_sound Tp Dp n i0 par (k0 + 1) h.2 k (by simpa using hk)
      rw [List.getD_cons_succ, show k0 + (k + 1) = k0 + 1 + k by omega]
      exact this

theorem treeOK_sound {Tp Dp n i0 : ℕ} {par : List (ℕ × ℕ)} (h : treeOK Tp Dp n i0 par = true) :
    ∀ k < par.length, (k = i0 ∧ get9 Dp k = 0) ∨ ((par.getD k (0, 0)).1 < n ∧ (par.getD k (0, 0)).2 < 4 ∧
      get9 Tp (4 * (par.getD k (0, 0)).1 + (par.getD k (0, 0)).2) = k ∧
      get9 Dp k = get9 Dp (par.getD k (0, 0)).1 + 1) := fun k hk => by
  simpa using treeAux_sound Tp Dp n i0 par 0 h k hk

theorem incrL_aux : ∀ (l : List ℕ) (p : ℕ), incrL l p = true → (∀ y ∈ l, p < y) ∧ l.Pairwise (· < ·)
  | [], _, _ => ⟨by simp, List.Pairwise.nil⟩
  | x :: l, p, h => by
    change (Nat.blt p x && incrL l x) = true at h
    rw [Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨h1, h2⟩ := incrL_aux l x h.2
    refine ⟨fun y hy => ?_, List.pairwise_cons.mpr ⟨h1, h2⟩⟩
    rcases List.mem_cons.mp hy with e | hy
    · exact e ▸ h.1
    · exact lt_trans h.1 (h1 y hy)

theorem incrL_sound {l : List ℕ} {p : ℕ} (h : incrL l p = true) : l.Pairwise (· < ·) := (incrL_aux l p h).2

theorem mwOK_sound {Ep n r0 r2 r3 u : ℕ} {VW : List ℕ} {mw : List (ℕ × List ℕ)}
    (h : mwOK Ep n r0 r2 r3 u VW mw = true) : mw.length = VW.length ∧ ∀ t < VW.length,
      ((mw.getD t (0, [])).1 < n ∧ getE Ep (mw.getD t (0, [])).1 = VW.getD t 0) ∨
        evalW r0 r2 r3 (VW.getD t 0) (mw.getD t (0, [])).2 idW = u := by
  induction VW generalizing mw with
  | nil =>
    cases mw with
    | nil => exact ⟨rfl, fun t ht => by simp at ht⟩
    | cons e mw => exact absurd h Bool.false_ne_true
  | cons x VW ih =>
    cases mw with
    | nil => exact absurd h Bool.false_ne_true
    | cons e mw =>
      change (mwRow Ep n r0 r2 r3 u x e && mwOK Ep n r0 r2 r3 u VW mw) = true at h
      rw [Bool.and_eq_true] at h
      obtain ⟨ih1, ih2⟩ := ih h.2
      refine ⟨by simp [ih1], fun t ht => ?_⟩
      cases t with
      | zero =>
        have h1 := h.1
        simp only [mwRow, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h1
        simpa using h1
      | succ t =>
        rw [List.getD_cons_succ, List.getD_cons_succ]
        exact ih2 t (by simpa using ht)

theorem ck51_sound {r0 r2 r3 Hp Tp i0 sa sb : ℕ} {H : List ℕ} (h : ck51 r0 r2 r3 H Hp Tp i0 sa sb = true) :
    i0 < H.length ∧ getE Hp i0 = idW ∧ elemsOK Hp Tp H.length [r0, r2, r3] H = true ∧ sa ≠ sb ∧
      commZ sa (zOf r0 r2 r3) = true ∧ commZ sb (zOf r0 r2 r3) = true ∧ sa ∉ H ∧ sb ∉ H := by
  simp only [ck51, witOK, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Bool.not_eq_true', beq_false_iff, lenL_eq,
    notIn_iff] at h
  obtain ⟨⟨⟨⟨hi, he⟩, hE⟩, hne⟩, ⟨⟨ha, hb⟩, hna⟩, hnb⟩ := h
  exact ⟨hi, he, hE, hne, ha, hb, hna, hnb⟩

theorem wfW_zero : wfW 0 = true := by
  rw [wfW_iff]
  exact ⟨by positivity, fun l _ => by rw [ln_zero]; norm_num⟩

theorem getD_wf {E : List ℕ} (h : ∀ x ∈ E, wfW x = true) (k : ℕ) : wfW (E.getD k 0) = true :=
  getD_prop (fun x => wfW x = true) E 0 k h wfW_zero

theorem getD_mem_of_lt {E : List ℕ} {k : ℕ} (hk : k < E.length) : E.getD k 0 ∈ E := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

variable {T : Set (owEm_GL 4)} {gs E : List ℕ}

theorem closure_sub_elems {Ep Tp n i0 : ℕ} (hE : elemsOK Ep Tp n gs E = true) (hn : n ≤ E.length) (hi0 : i0 < E.length)
    (hid : getE Ep i0 = idW) (hgs : ∀ x ∈ gs, wfW x = true)
    (hT : ∀ g ∈ T, ∃ c < gs.length, (g : Mat 4) = decW (gs.getD c 0)) :
    ∀ g ∈ Subgroup.closure T, ∃ k < E.length, (g : Mat 4) = decW (E.getD k 0) := by
  obtain ⟨hw, hel⟩ := elemsOK_sound hE
  have hM : ∀ g ∈ Submonoid.closure T, ∃ k < E.length, (g : Mat 4) = decW (E.getD k 0) := by
    intro g hg
    induction hg using Submonoid.closure_induction_left with
    | one => exact ⟨i0, hi0, by rw [← (hel i0 hi0).1, hid, decW_idW]; rfl⟩
    | mul_left x hx y _ ih =>
      obtain ⟨k, hk, ek⟩ := ih
      obtain ⟨c, hc, ec⟩ := hT x hx
      obtain ⟨ht, et⟩ := (hel k hk).2 c hc
      refine ⟨get9 Tp (4 * k + c), by omega, ?_⟩
      rw [Units.val_mul, ec, ek, ← (lmul_spec (getD_wf hgs c) (getD_wf hw k)).2, et, (hel _ (by omega)).1]
  intro g hg
  apply hM
  have hinv : ∀ x ∈ T, x⁻¹ ∈ Submonoid.closure T := fun x hx => by
    have hpos := orderOf_pos x
    have e : x⁻¹ = x ^ (orderOf x - 1) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
    rw [e]
    exact pow_mem (Submonoid.subset_closure hx) _
  have hsub : Submonoid.closure (T ∪ T⁻¹) ≤ Submonoid.closure T := by
    rw [Submonoid.closure_le]
    rintro x (hx | hx)
    · exact Submonoid.subset_closure hx
    · have := hinv _ (Set.mem_inv.mp hx)
      rwa [inv_inv] at this
  apply hsub
  rw [← Subgroup.closure_toSubmonoid]
  exact hg

theorem elems_sub_closure {Ep Tp Dp n i0 : ℕ} {par : List (ℕ × ℕ)} (hE : elemsOK Ep Tp n gs E = true)
    (htr : treeOK Tp Dp n i0 par = true) (hpar : par.length = E.length) (hn : n ≤ E.length)
    (hid : getE Ep i0 = idW) (hgs : ∀ x ∈ gs, wfW x = true) (hg4 : 4 ≤ gs.length)
    (hT : ∀ c < gs.length, ∃ g ∈ T, (g : Mat 4) = decW (gs.getD c 0)) :
    ∀ k < E.length, ∃ g ∈ Subgroup.closure T, (g : Mat 4) = decW (E.getD k 0) := by
  obtain ⟨hw, hel⟩ := elemsOK_sound hE
  have htr' := treeOK_sound htr
  have key : ∀ d k, get9 Dp k = d → k < E.length → ∃ g ∈ Subgroup.closure T, (g : Mat 4) = decW (E.getD k 0) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro k hd hk
      rcases htr' k (hpar ▸ hk) with ⟨rfl, -⟩ | ⟨hp, hc, hTk, hD⟩
      · exact ⟨1, one_mem _, by rw [← (hel k hk).1, hid, decW_idW]; rfl⟩
      · set p := (par.getD k (0, 0)).1
        set c := (par.getD k (0, 0)).2
        obtain ⟨g, hg, eg⟩ := ih (get9 Dp p) (by omega) p rfl (by omega)
        obtain ⟨u, hu, eu⟩ := hT c (by omega)
        refine ⟨u * g, mul_mem (Subgroup.subset_closure hu) hg, ?_⟩
        obtain ⟨-, et⟩ := (hel p (by omega)).2 c (by omega)
        rw [Units.val_mul, eu, eg, ← (lmul_spec (getD_wf hgs _) (getD_wf hw _)).2, et, hTk, (hel k hk).1]
  exact fun k hk => key _ k rfl hk

theorem card_closure_elems {Ep Tp Dp n i0 p : ℕ} {par : List (ℕ × ℕ)} (hE : elemsOK Ep Tp n gs E = true)
    (htr : treeOK Tp Dp n i0 par = true) (hinc : incrL E p = true) (hpar : par.length = E.length)
    (hn : n ≤ E.length) (hi0 : i0 < E.length) (hid : getE Ep i0 = idW) (hgs : ∀ x ∈ gs, wfW x = true)
    (hg4 : 4 ≤ gs.length) (hT : ∀ g ∈ T, ∃ c < gs.length, (g : Mat 4) = decW (gs.getD c 0))
    (hT' : ∀ c < gs.length, ∃ g ∈ T, (g : Mat 4) = decW (gs.getD c 0)) :
    Nat.card (Subgroup.closure T) = E.length := by
  have hw := (elemsOK_sound hE).1
  have h1 := closure_sub_elems hE hn hi0 hid hgs hT
  have h2 := elems_sub_closure hE htr hpar hn hid hgs hg4 hT'
  have himg : (Units.val '' (Subgroup.closure T : Set (owEm_GL 4))) = ((E.map decW).toFinset : Set (Mat 4)) := by
    ext M
    simp only [Set.mem_image, SetLike.mem_coe, Finset.mem_coe, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨k, hk, ek⟩ := h1 g hg
      exact ⟨_, getD_mem_of_lt hk, ek.symm⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
      obtain ⟨g, hg, eg⟩ := h2 k hk
      rw [List.getD_eq_getElem _ _ hk] at eg
      exact ⟨g, hg, eg⟩
  have hnd : (E.map decW).Nodup := by
    refine List.Nodup.map_on (fun a ha b hb hab => wfW_inj (hw a ha) (hw b hb) hab) ?_
    exact (incrL_sound hinc).imp (fun h => Nat.ne_of_lt h)
  calc Nat.card (Subgroup.closure T) = (Subgroup.closure T : Set (owEm_GL 4)).ncard := Nat.card_coe_set_eq _
    _ = (Units.val '' (Subgroup.closure T : Set (owEm_GL 4))).ncard :=
        (Set.ncard_image_of_injective _ Units.val_injective).symm
    _ = E.length := by
        rw [himg, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, List.length_map]

end CFSG.StandardType.ZS.B3MK

end
