module

public import Certificates.Data.Kernel.U43.Fast
public import CFSG.Certificates.Kernel.U43.Sound

public section

namespace CFSG.KC.U43

open Finset CFSG.KD.U43 CFSG.RankThree.PartTwo.Sec4.Item434RemU43

set_option exponentiation.threshold 1024
set_option maxRecDepth 20000

theorem letN_eq (v : ℕ) (k : ℕ → ℕ) : letN v k = k v := by
  cases v <;> rfl

@[expose] noncomputable def S (f : ℕ → ℕ) (n : ℕ) : ℕ := ∑ l ∈ range n, 2 ^ (16 * l) * f l

theorem S_succ (f : ℕ → ℕ) (n : ℕ) : S f (n + 1) = 2 ^ (16 * n) * f n + S f n := by
  rw [S, S, sum_range_succ, add_comm]

theorem S_zero (f : ℕ → ℕ) : S f 0 = 0 := by
  rw [S, sum_range_zero]

theorem S_succ' (f : ℕ → ℕ) : ∀ n : ℕ,
    S f (n + 1) = f 0 + 2 ^ 16 * S (fun l => f (l + 1)) n
  | 0 => by rw [S_succ, S_zero, S_zero]; ring
  | n + 1 => by
    rw [S_succ, S_succ' f n, S_succ (fun l => f (l + 1)) n, pow_succ', show 16 * (n + 1) = 16 + 16 * n by ring,
      pow_add]
    ring

theorem S_congr {f g : ℕ → ℕ} {n : ℕ} (h : ∀ l < n, f l = g l) : S f n = S g n :=
  sum_congr rfl fun l hl => by rw [h l (mem_range.1 hl)]

theorem S_add_fun (f g : ℕ → ℕ) (n : ℕ) : S f n + S g n = S (fun l => f l + g l) n := by
  simp only [S, ← sum_add_distrib, mul_add]

theorem S_mul (c : ℕ) (f : ℕ → ℕ) (n : ℕ) : c * S f n = S (fun l => c * f l) n := by
  simp only [S, mul_sum]
  exact sum_congr rfl fun l _ => by ring

theorem S_split (f : ℕ → ℕ) (a b : ℕ) :
    S f (a + b) = S f a + 2 ^ (16 * a) * S (fun l => f (a + l)) b := by
  rw [S, sum_range_add, S, S, mul_sum]
  congr 1
  refine sum_congr rfl fun l _ => ?_
  rw [mul_add, pow_add, mul_assoc]

theorem S_lt {f : ℕ → ℕ} (hf : ∀ l, f l < 2 ^ 16) : ∀ n, S f n < 2 ^ (16 * n)
  | 0 => by simp [S]
  | n + 1 => by
    rw [S_succ]
    have h1 := S_lt hf n
    have h2 : f n + 1 ≤ 2 ^ 16 := hf n
    calc 2 ^ (16 * n) * f n + S f n < 2 ^ (16 * n) * f n + 2 ^ (16 * n) := by omega
      _ = 2 ^ (16 * n) * (f n + 1) := by ring
      _ ≤ 2 ^ (16 * n) * 2 ^ 16 := Nat.mul_le_mul_left _ h2
      _ = 2 ^ (16 * (n + 1)) := by rw [← pow_add]; ring_nf

theorem testBit_S {f : ℕ → ℕ} (hf : ∀ l, f l < 2 ^ 16) (n q r : ℕ) (hr : r < 16) :
    (S f n).testBit (16 * q + r) = (decide (q < n) && (f q).testBit r) := by
  induction n with
  | zero => simp [S]
  | succ n ih =>
    rw [S_succ, Nat.testBit_two_pow_mul_add _ (S_lt hf n)]
    split_ifs with h
    · rw [ih]
      have : q < n := by omega
      simp [this, show q < n + 1 by omega]
    · by_cases hq : q = n
      · subst hq
        simp [show 16 * q + r - 16 * q = r by omega]
      · have hlt : f n < 2 ^ (16 * q + r - 16 * n) :=
          lt_of_lt_of_le (hf n) (Nat.pow_le_pow_right (by norm_num) (by omega))
        rw [Nat.testBit_lt_two_pow hlt]
        simp [show ¬ q < n + 1 by omega]

theorem eq_S {Z : ℕ} {g : ℕ → ℕ} (hg : ∀ l, g l < 2 ^ 16) (n : ℕ)
    (hZ : ∀ q r, r < 16 → Z.testBit (16 * q + r) = (decide (q < n) && (g q).testBit r)) :
    Z = S g n := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hr : i % 16 < 16 := Nat.mod_lt _ (by norm_num)
  rw [← Nat.div_add_mod i 16, hZ _ _ hr, testBit_S hg _ _ _ hr]

theorem t65535 {r : ℕ} (hr : r < 16) : (65535 : ℕ).testBit r = true := by
  rw [show (65535 : ℕ) = 2 ^ 16 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
  simpa using hr

theorem mask_S {X : ℕ → ℕ} (hX : ∀ l, X l < 2 ^ 16) (n k n' : ℕ) (p : ℕ → Bool) :
    (S X n >>> (16 * k)) &&& S (fun l => cond (p l) 65535 0) n' =
      S (fun l => cond (p l && decide (l + k < n)) (X (l + k)) 0) n' := by
  have hP : ∀ l, cond (p l) 65535 0 < 2 ^ 16 := fun l => by cases p l <;> simp
  have hQ : ∀ l, cond (p l && decide (l + k < n)) (X (l + k)) 0 < 2 ^ 16 := fun l => by
    cases (p l && decide (l + k < n))
    · simp
    · exact hX _
  apply eq_S hQ n'
  intro q r hr
  rw [Nat.testBit_and, Nat.testBit_shiftRight,
    show 16 * k + (16 * q + r) = 16 * (q + k) + r by ring, testBit_S hX _ _ _ hr,
    testBit_S hP _ _ _ hr]
  cases hp : p q <;> by_cases h1 : q + k < n <;> by_cases h2 : q < n' <;>
    simp [hp, h1, h2, t65535 hr]

theorem MCOL_eq : MCOL = S (fun l => cond (l % 4 == 0) 65535 0) 32 := by
  simp only [S, sum_range_succ, sum_range_zero]
  norm_num [MCOL]

theorem MROW_eq : MROW = S (fun l => cond (decide (l % 16 < 4)) 65535 0) 32 := by
  simp only [S, sum_range_succ, sum_range_zero]
  norm_num [MROW]

theorem M5_eq : M5 = S (fun _ => 31) 32 := by
  simp only [S, sum_range_succ, sum_range_zero]
  norm_num [M5]

theorem trm_S {X Y : ℕ → ℕ} (hX : ∀ l, X l < 2 ^ 16) (hY : ∀ l, Y l < 2 ^ 16) (k : ℕ) :
    trm (S X 32) (S Y 32) k =
      S (fun l => cond (l % 4 == 0 && decide (l + k < 32)) (X (l + k)) 0) 32 *
      S (fun l => cond (decide (l % 16 < 4) && decide (l + 4 * k < 32)) (Y (l + 4 * k)) 0) 32 := by
  change ((S X 32 >>> (16 * k)) &&& MCOL) * ((S Y 32 >>> (64 * k)) &&& MROW) = _
  rw [MCOL_eq, MROW_eq, show 64 * k = 16 * (4 * k) by ring, mask_S hX, mask_S hY]

@[expose] noncomputable def cv (X Y : ℕ → ℕ) (l : ℕ) : ℕ :=
  if l < 16 then ∑ k ∈ range 4, X (4 * (l / 4) + k) * Y (4 * k + l % 4)
  else if l < 32 then ∑ k ∈ range 4, (X (4 * ((l - 16) / 4) + k) * Y (16 + (4 * k + (l - 16) % 4)) +
    X (16 + (4 * ((l - 16) / 4) + k)) * Y (4 * k + (l - 16) % 4))
  else ∑ k ∈ range 4, X (16 + (4 * ((l - 32) / 4) + k)) * Y (16 + (4 * k + (l - 32) % 4))

theorem conv_eq (X Y : ℕ → ℕ) :
    S (fun l => cond (l % 4 == 0 && decide (l + 0 < 32)) (X (l + 0)) 0) 32 *
      S (fun l => cond (decide (l % 16 < 4) && decide (l + 4 * 0 < 32)) (Y (l + 4 * 0)) 0) 32 +
    S (fun l => cond (l % 4 == 0 && decide (l + 1 < 32)) (X (l + 1)) 0) 32 *
      S (fun l => cond (decide (l % 16 < 4) && decide (l + 4 * 1 < 32)) (Y (l + 4 * 1)) 0) 32 +
    (S (fun l => cond (l % 4 == 0 && decide (l + 2 < 32)) (X (l + 2)) 0) 32 *
      S (fun l => cond (decide (l % 16 < 4) && decide (l + 4 * 2 < 32)) (Y (l + 4 * 2)) 0) 32 +
    S (fun l => cond (l % 4 == 0 && decide (l + 3 < 32)) (X (l + 3)) 0) 32 *
      S (fun l => cond (decide (l % 16 < 4) && decide (l + 4 * 3 < 32)) (Y (l + 4 * 3)) 0) 32) =
    S (cv X Y) 48 := by
  simp only [S, cv, sum_range_succ, sum_range_zero]
  norm_num
  ring

theorem cv_le {X Y : ℕ → ℕ} (hX : ∀ l, X l ≤ 2) (hY : ∀ l, Y l ≤ 2) (l : ℕ) : cv X Y l ≤ 32 := by
  unfold cv
  split_ifs
  · calc _ ≤ ∑ k ∈ range 4, 2 * 2 := sum_le_sum fun k _ => Nat.mul_le_mul (hX _) (hY _)
      _ ≤ 32 := by simp
  · calc _ ≤ ∑ k ∈ range 4, (2 * 2 + 2 * 2) := sum_le_sum fun k _ =>
          Nat.add_le_add (Nat.mul_le_mul (hX _) (hY _)) (Nat.mul_le_mul (hX _) (hY _))
      _ ≤ 32 := by simp
  · calc _ ≤ ∑ k ∈ range 4, 2 * 2 := sum_le_sum fun k _ => Nat.mul_le_mul (hX _) (hY _)
      _ ≤ 32 := by simp

theorem cv_le16 {X Y : ℕ → ℕ} (hX : ∀ l, X l ≤ 2) (hY : ∀ l, Y l ≤ 2) {l : ℕ}
    (hl : l < 16 ∨ 32 ≤ l) : cv X Y l ≤ 16 := by
  unfold cv
  split_ifs with h1 h2
  · calc _ ≤ ∑ k ∈ range 4, 2 * 2 := sum_le_sum fun k _ => Nat.mul_le_mul (hX _) (hY _)
      _ ≤ 16 := by simp
  · omega
  · calc _ ≤ ∑ k ∈ range 4, 2 * 2 := sum_le_sum fun k _ => Nat.mul_le_mul (hX _) (hY _)
      _ ≤ 16 := by simp

theorem fold3_S {C : ℕ → ℕ} (hC : ∀ l, C l < 2 ^ 16) :
    fold3 (S C 48) = S (fun l => if l < 16 then C l + 2 * C (32 + l) else C l) 32 := by
  have hs : S C 48 = S C 16 + 2 ^ 256 * (S (fun l => C (16 + l)) 16 +
      2 ^ 256 * S (fun l => C (32 + l)) 16) := by
    rw [show 48 = 16 + (16 + 16) by rfl, S_split, S_split]
    simp only [← Nat.add_assoc]
  have hA : S C 16 < 2 ^ 256 := S_lt hC 16
  have hB : S (fun l => C (16 + l)) 16 < 2 ^ 256 := S_lt (fun l => hC (16 + l)) 16
  have hL : L256 = 2 ^ 256 - 1 := by decide +kernel
  have p : (2 : ℕ) ^ 512 = 2 ^ 256 * 2 ^ 256 := by norm_num
  have h0 : (0 : ℕ) < 2 ^ 256 := by norm_num
  have h1 : S C 48 % 2 ^ 256 = S C 16 := by
    rw [hs, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hA]
  have h2 : S C 48 / 2 ^ 256 = S (fun l => C (16 + l)) 16 + 2 ^ 256 * S (fun l => C (32 + l)) 16 := by
    rw [hs, Nat.add_mul_div_left _ _ h0, Nat.div_eq_of_lt hA, Nat.zero_add]
  have h3 : S C 48 / 2 ^ 512 = S (fun l => C (32 + l)) 16 := by
    rw [p, ← Nat.div_div_eq_div_mul, h2, Nat.add_mul_div_left _ _ h0, Nat.div_eq_of_lt hB,
      Nat.zero_add]
  have h4 : S C 48 / 2 ^ 256 % 2 ^ 256 = S (fun l => C (16 + l)) 16 := by
    rw [h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hB]
  change (S C 48 &&& L256) + ((S C 48 >>> 512) <<< 1) + (((S C 48 >>> 256) &&& L256) <<< 256) = _
  rw [hL, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.shiftLeft_eq, h1, h3, h4,
    show 32 = 16 + 16 by rfl, S_split]
  have e1 : S (fun l => if l < 16 then C l + 2 * C (32 + l) else C l) 16 =
      S C 16 + 2 * S (fun l => C (32 + l)) 16 := by
    rw [S_mul, S_add_fun]
    exact S_congr fun l hl => by rw [if_pos hl]
  have e2 : S (fun l => (fun l => if l < 16 then C l + 2 * C (32 + l) else C l) (16 + l)) 16 =
      S (fun l => C (16 + l)) 16 :=
    S_congr fun l _ => by simp
  rw [e1, e2]
  norm_num
  ring

theorem red3_S {W : ℕ → ℕ} (hW : ∀ l, W l ≤ 48) : red3 (S W 32) = S (fun l => W l % 3) 32 := by
  have hW' : ∀ l, 43 * W l < 2 ^ 16 := fun l => by
    have := hW l
    omega
  have hq : ∀ l, 43 * W l / 128 < 2 ^ 16 := fun l => by
    have := hW l
    omega
  have h31 : ∀ l : ℕ, (fun _ => 31) l < 2 ^ 16 := fun _ => by norm_num
  have hm : ((S W 32 * 43) >>> 7) &&& M5 = S (fun l => 43 * W l / 128) 32 := by
    rw [mul_comm, S_mul]
    apply eq_S hq 32
    intro q r hr
    rw [Nat.testBit_and, Nat.testBit_shiftRight, M5_eq, testBit_S h31 _ _ _ hr]
    by_cases h5 : r < 5
    · rw [show 7 + (16 * q + r) = 16 * q + (r + 7) by ring, testBit_S hW' _ _ _ (by omega)]
      have e : 43 * W q / 128 = 43 * W q / 2 ^ 7 := by norm_num
      have t31 : (31 : ℕ).testBit r = true := by
        rw [show (31 : ℕ) = 2 ^ 5 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
        simpa using h5
      rw [e, Nat.testBit_div_two_pow, t31]
      by_cases hq : q < 32 <;> simp [hq]
    · have t31 : (31 : ℕ).testBit r = false := by
        rw [show (31 : ℕ) = 2 ^ 5 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
        simpa using h5
      have hlt : 43 * W q / 128 < 2 ^ r := by
        have := hW q
        have : 2 ^ 5 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      rw [t31, Nat.testBit_lt_two_pow hlt]
      simp
  change S W 32 - 3 * (((S W 32 * 43) >>> 7) &&& M5) = _
  rw [hm, S_mul]
  apply Nat.sub_eq_of_eq_add
  rw [S_add_fun]
  exact S_congr fun l _ => by
    have := hW l
    omega

theorem lanes_S (L : List ℕ) : lanes L = S (fun l => L.getD l 0) L.length := by
  induction L with
  | nil => rfl
  | cons r t ih =>
    rw [List.length_cons, S_succ']
    change r + (lanes t <<< 16) = _
    rw [Nat.shiftLeft_eq, ih, mul_comm]
    simp

@[expose] noncomputable def XF (c : List ℕ) (l : ℕ) : ℕ :=
  if l < 16 then c.getD l 0 / 3 else c.getD (l - 16) 0 % 3

theorem getD_lt9 {L : List ℕ} (h : canon4 L = true) (i : ℕ) : L.getD i 0 < 9 := by
  rcases Nat.lt_or_ge i L.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    exact (canon4_iff.1 h).2 _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ hi]
    norm_num

theorem getD_map0 (L : List ℕ) (f : ℕ → ℕ) (hf : f 0 = 0) (i : ℕ) :
    (L.map f).getD i 0 = f (L.getD i 0) := by
  rcases Nat.lt_or_ge i L.length with hi | hi
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi,
      List.getElem_map]
  · rw [List.getD_eq_default _ _ (by simpa using hi), List.getD_eq_default _ _ hi, hf]

theorem XF_le {c : List ℕ} (h : canon4 c = true) (l : ℕ) : XF c l ≤ 2 := by
  unfold XF
  split_ifs
  · have := getD_lt9 h l
    omega
  · have := getD_lt9 h (l - 16)
    omega

theorem XF_lo {c : List ℕ} {i : ℕ} (h : i < 16) : XF c i = c.getD i 0 / 3 := by
  rw [XF, if_pos h]

theorem XF_hi (c : List ℕ) (i : ℕ) : XF c (16 + i) = c.getD i 0 % 3 := by
  rw [XF, if_neg (by omega), Nat.add_sub_cancel_left]

theorem lanes_lo {c : List ℕ} (hl : c.length = 16) :
    lanes (c.map fun e => e / 3) = S (XF c) 16 := by
  rw [lanes_S, List.length_map, hl]
  exact S_congr fun l hl' => by rw [getD_map0 c _ (Nat.zero_div 3), XF_lo hl']

theorem lanes_hi {c : List ℕ} (hl : c.length = 16) :
    lanes (c.map fun e => e % 3) = S (fun l => XF c (16 + l)) 16 := by
  rw [lanes_S, List.length_map, hl]
  exact S_congr fun l _ => by rw [getD_map0 c _ (Nat.zero_mod 3), XF_hi]

theorem fmtF_eq (c : List ℕ) :
    fmtF c = lanes (c.map fun e => e / 3) + lanes (c.map fun e => e % 3) * 2 ^ 256 := by
  have e : fmtF c = lanes (c.map fun e => e / 3) + (lanes (c.map fun e => e % 3) <<< 256) := rfl
  rewrite [e, Nat.shiftLeft_eq]
  rfl

theorem fmtF_S {c : List ℕ} (h : canon4 c = true) : fmtF c = S (XF c) 32 := by
  have hl : c.length = 16 := (canon4_iff.1 h).1
  rw [fmtF_eq, lanes_lo hl, lanes_hi hl, show (32 : ℕ) = 16 + 16 from rfl, S_split,
    show 16 * 16 = 256 from rfl, Nat.mul_comm (2 ^ 256)]

theorem addC_f (p q p' q' : ℕ) :
    addC (3 * (p % 3) + q % 3) (3 * (p' % 3) + q' % 3) = 3 * ((p + p') % 3) + (q + q') % 3 := by
  unfold addC
  omega

theorem mulC_f (a b : ℕ) : mulC a b =
    3 * ((a / 3 * (b / 3) + 2 * (a % 3 * (b % 3))) % 3) + (a / 3 * (b % 3) + a % 3 * (b / 3)) % 3 :=
  rfl

theorem ent_f (a0 a1 a2 a3 b0 b1 b2 b3 : ℕ) :
    addC (addC (addC (mulC a0 b0) (mulC a1 b1)) (mulC a2 b2)) (mulC a3 b3) =
      3 * ((a0 / 3 * (b0 / 3) + 2 * (a0 % 3 * (b0 % 3)) + (a1 / 3 * (b1 / 3) + 2 * (a1 % 3 * (b1 % 3))) +
        (a2 / 3 * (b2 / 3) + 2 * (a2 % 3 * (b2 % 3))) + (a3 / 3 * (b3 / 3) + 2 * (a3 % 3 * (b3 % 3))))
          % 3) +
      ((a0 / 3 * (b0 % 3) + a0 % 3 * (b0 / 3)) + (a1 / 3 * (b1 % 3) + a1 % 3 * (b1 / 3)) +
        (a2 / 3 * (b2 % 3) + a2 % 3 * (b2 / 3)) + (a3 / 3 * (b3 % 3) + a3 % 3 * (b3 / 3))) % 3 := by
  rw [mulC_f a0, mulC_f a1, mulC_f a2, mulC_f a3, addC_f, addC_f, addC_f]

theorem div_f (R I : ℕ) : (3 * (R % 3) + I % 3) / 3 = R % 3 := by omega

theorem mod_f (R I : ℕ) : (3 * (R % 3) + I % 3) % 3 = I % 3 := by omega

theorem getD_mul4 (a b : List ℕ) {l : ℕ} (hl : l < 16) : (mul4 a b).getD l 0 =
    addC (addC (addC (mulC (a.getD (4 * (l / 4)) 0) (b.getD (l % 4) 0))
      (mulC (a.getD (4 * (l / 4) + 1) 0) (b.getD (4 + l % 4) 0)))
      (mulC (a.getD (4 * (l / 4) + 2) 0) (b.getD (8 + l % 4) 0)))
      (mulC (a.getD (4 * (l / 4) + 3) 0) (b.getD (12 + l % 4) 0)) := by
  simp only [mul4, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl,
    Option.map_some, Option.getD_some, Array.getD_eq_getD_getElem?, List.getElem?_toArray]

theorem lane_eq {m n : List ℕ} {l : ℕ} (hl : l < 32) :
    (if l < 16 then cv (XF m) (XF n) l + 2 * cv (XF m) (XF n) (32 + l) else cv (XF m) (XF n) l) % 3 =
      XF (mul4 m n) l := by
  by_cases h : l < 16
  · rw [if_pos h, XF_lo h, getD_mul4 m n h, ent_f, div_f]
    have e1 : ¬ 32 + l < 16 := by omega
    have e2 : ¬ 32 + l < 32 := by omega
    simp only [cv, if_pos h, e1, e2, if_false, Nat.add_sub_cancel_left, sum_range_succ,
      sum_range_zero, XF_hi]
    simp (disch := omega) only [XF_lo]
    ring_nf
  · obtain ⟨l', rfl⟩ : ∃ l', l = 16 + l' := ⟨l - 16, by omega⟩
    have hl' : l' < 16 := by omega
    rw [if_neg h, XF_hi, getD_mul4 m n hl', ent_f, mod_f]
    simp only [cv, h, hl, if_false, if_true, Nat.add_sub_cancel_left, sum_range_succ, sum_range_zero,
      XF_hi]
    simp (disch := omega) only [XF_lo]
    ring_nf

theorem MF_fmtF {m n : List ℕ} (hm : canon4 m = true) (hn : canon4 n = true) :
    MF (fmtF m) (fmtF n) = fmtF (mul4 m n) := by
  have hX := XF_le hm
  have hY := XF_le hn
  have hX' : ∀ l, XF m l < 2 ^ 16 := fun l => by
    have := hX l
    omega
  have hY' : ∀ l, XF n l < 2 ^ 16 := fun l => by
    have := hY l
    omega
  have hC : ∀ l, cv (XF m) (XF n) l < 2 ^ 16 := fun l => by
    have := cv_le hX hY l
    omega
  have hW : ∀ l, (if l < 16 then cv (XF m) (XF n) l + 2 * cv (XF m) (XF n) (32 + l)
      else cv (XF m) (XF n) l) ≤ 48 := fun l => by
    split_ifs with h
    · have := cv_le16 hX hY (Or.inl h)
      have := cv_le16 hX hY (l := 32 + l) (Or.inr (by omega))
      omega
    · have := cv_le hX hY l
      omega
  rw [fmtF_S hm, fmtF_S hn, fmtF_S (canon4_mul4 m n)]
  unfold MF
  simp only [letN_eq]
  change red3 (fold3 ((trm (S (XF m) 32) (S (XF n) 32) 0 + trm (S (XF m) 32) (S (XF n) 32) 1) +
    (trm (S (XF m) 32) (S (XF n) 32) 2 + trm (S (XF m) 32) (S (XF n) 32) 3))) = _
  rw [trm_S hX' hY', trm_S hX' hY', trm_S hX' hY', trm_S hX' hY', conv_eq, fold3_S hC, red3_S hW]
  exact S_congr fun l hl => lane_eq hl

theorem S_inj {f g : ℕ → ℕ} (hf : ∀ l, f l < 2 ^ 16) (hg : ∀ l, g l < 2 ^ 16) {n : ℕ}
    (h : S f n = S g n) {l : ℕ} (hl : l < n) : f l = g l := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < 16
  · have := testBit_S hf n l r hr
    rw [h, testBit_S hg n l r hr] at this
    simpa [hl] using this.symm
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (hf l) (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (hg l) (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem fmtF_inj {a b : List ℕ} (ha : canon4 a = true) (hb : canon4 b = true)
    (h : fmtF a = fmtF b) : a = b := by
  rw [fmtF_S ha, fmtF_S hb] at h
  have hX : ∀ l, XF a l < 2 ^ 16 := fun l => by
    have := XF_le ha l
    omega
  have hY : ∀ l, XF b l < 2 ^ 16 := fun l => by
    have := XF_le hb l
    omega
  have la := (canon4_iff.1 ha).1
  have lb := (canon4_iff.1 hb).1
  apply List.ext_getElem (by rw [la, lb])
  intro i hi hi'
  have h1 := S_inj hX hY h (l := i) (by omega)
  have h2 := S_inj hX hY h (l := 16 + i) (by omega)
  rw [XF_lo (by omega), XF_lo (by omega), List.getD_eq_getElem _ _ hi,
    List.getD_eq_getElem _ _ hi'] at h1
  rw [XF_hi, XF_hi, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] at h2
  omega

@[expose] def DatF (c : List ℕ) (C : ℕ) : Prop := canon4 c = true ∧ fmtF c = C

theorem mulDF {a b : List ℕ} {A B : ℕ} (ha : DatF a A) (hb : DatF b B) :
    DatF (mul4 a b) (MF A B) :=
  ⟨canon4_mul4 a b, by rw [← ha.2, ← hb.2, MF_fmtF ha.1 hb.1]⟩

theorem beqDF {a b : List ℕ} {A B : ℕ} (ha : DatF a A) (hb : DatF b B) :
    (a == b) = Nat.beq A B := by
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, Nat.beq_eq, ← ha.2, ← hb.2]
  exact ⟨fun h => h ▸ rfl, fmtF_inj ha.1 hb.1⟩

theorem oneDF : DatF one4 ONEF := ⟨canon4_one4, by decide +kernel⟩

theorem letDF {A : ℕ → ℕ} (hA : lettersF A = true) (l : ℕ) : DatF (letterCode l) (letP A l) := by
  have h4 := CFSG.KC.G2Three.allBelow_g2 hA (by decide)
  have hs : ∀ s < 4, DatF (letterCode s) (A s) := fun s hs =>
    ⟨canon4_letterCode s, Nat.eq_of_beq_eq_true (h4 s hs)⟩
  unfold letP
  by_cases hl : l < 3
  · rw [Nat.blt_eq.mpr hl, cond_true]
    exact hs l (by omega)
  · have hb : Nat.blt l 3 = false := by
      cases hq : Nat.blt l 3
      · rfl
      · exact absurd (Nat.blt_eq.mp hq) hl
    rw [hb, cond_false]
    have e : letterCode l = letterCode 3 := by
      unfold letterCode
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rfl
    rw [e]
    exact hs 3 (by omega)

theorem foldDF {A : ℕ → ℕ} (hA : lettersF A = true) :
    ∀ (w : List ℕ) (acc : List ℕ) (C : ℕ), DatF acc C →
      DatF (w.foldl (fun c l => mul4 c (letterCode l)) acc)
        (w.foldl (fun c l => MF c (letP A l)) C)
  | [], _, _, h => h
  | l :: w, acc, C, h => foldDF hA w _ _ (mulDF h (letDF hA l))

theorem wordDF {A : ℕ → ℕ} (hA : lettersF A = true) (w : List ℕ) :
    DatF (wordCode w) (wordF A w) :=
  foldDF hA w one4 ONEF oneDF

theorem conjDF {A : ℕ → ℕ} (hA : lettersF A = true) (w : List ℕ) {x : List ℕ} {X : ℕ}
    (hx : DatF x X) :
    DatF (conjStep (wordPair w) x) (MF (MF (wordF A w) X) (wordF A (invWord w))) := by
  have hw := wordDF hA w
  have hl : (wordCode w).length = 16 := (canon4_iff.1 hw.1).1
  unfold conjStep wordPair
  rw [List.take_left' hl, List.drop_left' hl]
  exact mulDF (mulDF hw hx) (wordDF hA (invWord w))

end CFSG.KC.U43

end
