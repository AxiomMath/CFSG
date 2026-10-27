module

public import CFSG.Certificates.Kernel.U35Pk.Lanes
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Certificates.U35Pk

open CFSG.RankThree.PartOne.HNB Matrix

set_option exponentiation.threshold 2100

theorem ev_of_zero : ∀ {n : ℕ} {W : ℕ → ℕ}, (∀ m, W m = 0) → ev W n = 0
  | 0, _, _ => rfl
  | n + 1, W, h => by
    rw [ev_succ, h 0, ev_of_zero fun m => h (m + 1)]
    rfl

theorem ev_congr : ∀ {n : ℕ} {W V : ℕ → ℕ}, (∀ m < n, W m = V m) → ev W n = ev V n
  | 0, _, _, _ => rfl
  | n + 1, W, V, h => by
    rw [ev_succ, ev_succ, h 0 (by omega), ev_congr fun m hm => h (m + 1) (by omega)]

theorem ev_extend : ∀ {m m' : ℕ} {W : ℕ → ℕ}, (∀ ℓ, m ≤ ℓ → W ℓ = 0) → m ≤ m' →
    ev W m' = ev W m
  | 0, _, _, h, _ => by
    rw [ev_of_zero fun ℓ => h ℓ (Nat.zero_le ℓ)]
    rfl
  | m + 1, 0, _, _, hm => absurd hm (by omega)
  | m + 1, m' + 1, W, h, hm => by
    rw [ev_succ, ev_succ, ev_extend (fun ℓ hℓ => h (ℓ + 1) (by omega)) (by omega : m ≤ m')]

@[expose] def cv (W V : ℕ → ℕ) (ℓ : ℕ) : ℕ := ∑ a ∈ Finset.range (ℓ + 1), W a * V (ℓ - a)

theorem cv_zero (W V : ℕ → ℕ) : cv W V 0 = W 0 * V 0 := by simp [cv]

theorem cv_succ (W V : ℕ → ℕ) (ℓ : ℕ) :
    cv W V (ℓ + 1) = W 0 * V (ℓ + 1) + cv (fun a => W (a + 1)) V ℓ := by
  unfold cv
  rw [Finset.sum_range_succ']
  simp only [Nat.add_sub_add_right, Nat.sub_zero]
  ring

theorem cv_le {W V : ℕ → ℕ} {A B : ℕ} (hW : ∀ a, W a ≤ A) (hV : ∀ b, V b ≤ B) (ℓ : ℕ) :
    cv W V ℓ ≤ (ℓ + 1) * (A * B) := by
  unfold cv
  calc ∑ a ∈ Finset.range (ℓ + 1), W a * V (ℓ - a) ≤ ∑ _a ∈ Finset.range (ℓ + 1), A * B :=
        Finset.sum_le_sum fun a _ => Nat.mul_le_mul (hW a) (hV _)
    _ = (ℓ + 1) * (A * B) := by simp

theorem ev_mul_ev {V : ℕ → ℕ} {m : ℕ} (hV : ∀ b, m ≤ b → V b = 0) :
    ∀ {n : ℕ} {W : ℕ → ℕ}, (∀ a, n ≤ a → W a = 0) → ev W n * ev V m = ev (cv W V) (n + m)
  | 0, W, hW => by
    rw [ev_zero, Nat.zero_mul, Nat.zero_add, ev_of_zero]
    intro ℓ
    simp [cv, hW _ (Nat.zero_le _)]
  | n + 1, W, hW => by
    have ih := ev_mul_ev hV (n := n) (W := fun a => W (a + 1)) fun a ha => hW (a + 1) (by omega)
    have h2 : ev V m = V 0 + 2 ^ 18 * ev (fun b => V (b + 1)) (n + m) := by
      rw [← ev_succ]
      exact (ev_extend hV (by omega)).symm
    have h3 : (fun ℓ => cv W V (ℓ + 1)) = fun ℓ => W 0 * V (ℓ + 1) + cv (fun a => W (a + 1)) V ℓ :=
      funext (cv_succ W V)
    rw [Nat.add_right_comm, ev_succ (cv W V), h3, ev_add, ev_mul, ← ih, cv_zero, ev_succ W, h2]
    ring

theorem ev_div : ∀ {s n : ℕ} {W : ℕ → ℕ}, (∀ m < n, W m < 2 ^ 18) → s ≤ n →
    ev W n / 2 ^ (18 * s) = ev (fun ℓ => W (ℓ + s)) (n - s)
  | 0, n, W, _, _ => by simp
  | s + 1, 0, _, _, hs => absurd hs (by omega)
  | s + 1, n + 1, W, hW, hs => by
    have e : 18 * (s + 1) = 18 + 18 * s := by ring
    rw [ev_succ, e, Nat.pow_add, ← Nat.div_div_eq_div_mul, split_div (hW 0 (by omega)),
      ev_div (fun m hm => hW (m + 1) (by omega)) (by omega : s ≤ n)]
    have e2 : n + 1 - (s + 1) = n - s := by omega
    rw [e2]
    apply ev_congr
    intro m _
    congr 1

theorem two_pow_mod_split {a b p q : ℕ} (ha : a < 2 ^ p) :
    (a + 2 ^ p * b) % 2 ^ (p + q) = a + 2 ^ p * (b % 2 ^ q) := by
  have e : a + 2 ^ p * b = (a + 2 ^ p * (b % 2 ^ q)) + 2 ^ (p + q) * (b / 2 ^ q) := by
    conv_lhs => rw [← Nat.mod_add_div b (2 ^ q)]
    rw [Nat.pow_add]
    ring
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (add_two_pow_mul_lt ha (Nat.mod_lt _ (by positivity)))]

theorem ev_mod : ∀ {t n : ℕ} {W : ℕ → ℕ}, (∀ m < n, W m < 2 ^ 18) → t ≤ n →
    ev W n % 2 ^ (18 * t) = ev W t
  | 0, n, W, _, _ => by simp [ev, Nat.mod_one]
  | t + 1, 0, _, _, ht => absurd ht (by omega)
  | t + 1, n + 1, W, hW, ht => by
    have e : 18 * (t + 1) = 18 + 18 * t := by ring
    rw [ev_succ, ev_succ, e, two_pow_mod_split (hW 0 (by omega)),
      ev_mod (fun m hm => hW (m + 1) (by omega)) (by omega : t ≤ n)]

theorem ev_window {n p : ℕ} (s : ℕ) {W : ℕ → ℕ} (hW : ∀ m < n, W m < 2 ^ 18) (hp : p = 18 * s)
    (hs : s + 3 ≤ n) :
    ev W n / 2 ^ p % 2 ^ 54 = W s + 2 ^ 18 * W (s + 1) + 2 ^ 36 * W (s + 2) := by
  subst hp
  have e : (54 : ℕ) = 18 * 3 := by norm_num
  rw [ev_div hW (by omega), e, ev_mod (fun m hm => hW (m + s) (by omega)) (by omega)]
  simp only [ev_succ, ev_zero]
  ring_nf

theorem testBit_div_mod (N t w b : ℕ) :
    (N / 2 ^ t % 2 ^ w).testBit b = (decide (b < w) && N.testBit (b + t)) := by
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]

theorem testBit_split {lo : ℕ} (hi : ℕ) (h : lo < 2 ^ 1024) (i : ℕ) :
    (lo + 2 ^ 1024 * hi).testBit i = if i < 1024 then lo.testBit i else hi.testBit (i - 1024) := by
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ h]

theorem window_lo {lo : ℕ} (hi : ℕ) (hlo : lo < 2 ^ 1024) {s t : ℕ} (h : s + t + 54 ≤ 1024) :
    (lo + 2 ^ 1024 * hi) / 2 ^ s % 2 ^ 1024 / 2 ^ t % 2 ^ 54 = lo / 2 ^ (s + t) % 2 ^ 54 := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_div_mod, testBit_div_mod, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    testBit_split _ hlo]
  by_cases hb : b < 54
  · have h1 : b + t < 1024 := by omega
    have h2 : b + t + s < 1024 := by omega
    have h3 : b + t + s = b + (s + t) := by omega
    have h4 : ¬ 1024 ≤ b + (s + t) := by omega
    simp [hb, h1, h2, h3, h4]
  · simp [hb]

theorem window_lo0 {lo : ℕ} (hi : ℕ) (hlo : lo < 2 ^ 1024) {s : ℕ} (h : s + 54 ≤ 1024) :
    (lo + 2 ^ 1024 * hi) / 2 ^ s % 2 ^ 1024 % 2 ^ 54 = lo / 2 ^ s % 2 ^ 54 := by
  have := window_lo hi hlo (t := 0) (s := s) (by omega)
  simpa using this

theorem window_hi {lo : ℕ} (hi : ℕ) (hlo : lo < 2 ^ 1024) (s t : ℕ) :
    (lo + 2 ^ 1024 * hi) / 2 ^ s / 2 ^ 1024 / 2 ^ t = hi / 2 ^ (s + t) := by
  rw [Nat.div_div_eq_div_mul _ (2 ^ s) (2 ^ 1024), Nat.mul_comm (2 ^ s) (2 ^ 1024),
    ← Nat.div_div_eq_div_mul, split_div hlo,
    Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem lor_split {a c : ℕ} (b d : ℕ) (ha : a < 2 ^ 1024) (hc : c < 2 ^ 1024) :
    (a + 2 ^ 1024 * b) ||| (c + 2 ^ 1024 * d) = (a ||| c) + 2 ^ 1024 * (b ||| d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, testBit_split _ ha, testBit_split _ hc,
    testBit_split _ (Nat.or_lt_two_pow ha hc)]
  split_ifs <;> simp

theorem mul_lor (p x y : ℕ) : 2 ^ p * x ||| 2 ^ p * y = 2 ^ p * (x ||| y) := by
  rw [Nat.mul_comm, Nat.mul_comm _ y, Nat.mul_comm _ (x ||| y), ← Nat.shiftLeft_eq,
    ← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq, Nat.shiftLeft_or_distrib]

theorem lor_add {x y : ℕ} (p : ℕ) (hy : y < 2 ^ p) : 2 ^ p * x ||| y = 2 ^ p * x + y :=
  (Nat.two_pow_add_eq_or_of_lt hy x).symm

@[expose] def foldP (y : ℕ) : ℕ := y % 2 ^ 2048 + 2 * (y / 2 ^ 2048)

@[expose] def M0 : ℕ := 2 ^ 108 * (2 ^ 54 - 1)

@[expose] def M1 : ℕ := 2 ^ 54 * (2 ^ 54 - 1)

@[expose] def M2 : ℕ := 2 ^ 54 - 1

@[expose] def gatherP (z : ℕ) : ℕ :=
  (z &&& (M0 + 2 ^ 1024 * M0)) ||| (z / 2 ^ 324 &&& (M1 + 2 ^ 1024 * M1)) |||
    (z / 2 ^ 648 &&& (M2 + 2 ^ 1024 * M2))

@[expose] def LANE : ℕ := ev (fun _ => 255) 9

@[expose] def redP (x : ℕ) : ℕ := x - 5 * (x * 205 / 2 ^ 10 &&& (LANE + 2 ^ 1024 * LANE))

@[expose] def mulP (a b : ℕ) : ℕ := redP (gatherP (foldP (a * b)))

theorem foldP_eq {P M : ℕ} (Q : ℕ) (hP : P < 2 ^ 1024) (hM : M < 2 ^ 1024) :
    foldP (P + 2 ^ 1024 * M + 2 ^ 2048 * Q) = (P + 2 * Q) + 2 ^ 1024 * M := by
  have h : P + 2 ^ 1024 * M < 2 ^ 2048 := add_two_pow_mul_lt hP hM
  unfold foldP
  rw [split_mod h, split_div h]
  ring

theorem gatherP_eq {lo : ℕ} (hi : ℕ) (hlo : lo < 2 ^ 1024) :
    gatherP (lo + 2 ^ 1024 * hi) =
      (2 ^ 108 * (lo / 2 ^ 108 % 2 ^ 54) + 2 ^ 54 * (lo / 2 ^ 378 % 2 ^ 54) + lo / 2 ^ 648 % 2 ^ 54) +
        2 ^ 1024 * (2 ^ 108 * (hi / 2 ^ 108 % 2 ^ 54) + 2 ^ 54 * (hi / 2 ^ 378 % 2 ^ 54) +
          hi / 2 ^ 648 % 2 ^ 54) := by
  have hM0 : M0 < 2 ^ 1024 := by unfold M0; norm_num
  have hM1 : M1 < 2 ^ 1024 := by unfold M1; norm_num
  have hM2 : M2 < 2 ^ 1024 := by unfold M2; norm_num
  unfold gatherP
  rw [land_split _ _ _ _ hM0, land_split _ _ _ _ hM1, land_split _ _ _ _ hM2]
  rw [split_mod hlo, split_div hlo]
  unfold M0 M1 M2
  rw [land_shift_mask, land_shift_mask, land_shift_mask, land_shift_mask,
    Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
  rw [window_lo hi hlo (by norm_num), window_lo0 hi hlo (by norm_num)]
  have e1 : (lo + 2 ^ 1024 * hi) / 2 ^ 324 / 2 ^ 1024 / 2 ^ 54 = hi / 2 ^ 378 :=
    window_hi hi hlo 324 54
  have e2 : (lo + 2 ^ 1024 * hi) / 2 ^ 648 / 2 ^ 1024 = hi / 2 ^ 648 := by
    have := window_hi hi hlo 648 0
    simpa using this
  rw [e1, e2]
  have b1 : ∀ x : ℕ, x % 2 ^ 54 < 2 ^ 54 := fun x => Nat.mod_lt _ (by positivity)
  have a0 : ∀ x : ℕ, 2 ^ 108 * (x % 2 ^ 54) < 2 ^ 1024 := fun x => by
    have := b1 x
    calc 2 ^ 108 * (x % 2 ^ 54) < 2 ^ 108 * 2 ^ 54 := Nat.mul_lt_mul_of_pos_left this (by positivity)
      _ ≤ 2 ^ 1024 := by norm_num
  have a1 : ∀ x : ℕ, 2 ^ 54 * (x % 2 ^ 54) < 2 ^ 1024 := fun x => by
    have := b1 x
    calc 2 ^ 54 * (x % 2 ^ 54) < 2 ^ 54 * 2 ^ 54 := Nat.mul_lt_mul_of_pos_left this (by positivity)
      _ ≤ 2 ^ 1024 := by norm_num
  have a2 : ∀ x : ℕ, x % 2 ^ 54 < 2 ^ 1024 := fun x =>
    lt_of_lt_of_le (b1 x) (by norm_num)
  rw [lor_split _ _ (a0 _) (a1 _)]
  have c01 : ∀ x y : ℕ, 2 ^ 108 * (x % 2 ^ 54) ||| 2 ^ 54 * (y % 2 ^ 54) =
      2 ^ 108 * (x % 2 ^ 54) + 2 ^ 54 * (y % 2 ^ 54) := fun x y => by
    have e : 2 ^ 108 * (x % 2 ^ 54) = 2 ^ 54 * (2 ^ 54 * (x % 2 ^ 54)) := by ring
    rw [e, mul_lor, lor_add _ (b1 y), Nat.mul_add]
  have c2 : ∀ x y z : ℕ, (2 ^ 108 * (x % 2 ^ 54) + 2 ^ 54 * (y % 2 ^ 54)) ||| z % 2 ^ 54 =
      2 ^ 108 * (x % 2 ^ 54) + 2 ^ 54 * (y % 2 ^ 54) + z % 2 ^ 54 := fun x y z => by
    have e : 2 ^ 108 * (x % 2 ^ 54) + 2 ^ 54 * (y % 2 ^ 54) =
        2 ^ 54 * (2 ^ 54 * (x % 2 ^ 54) + y % 2 ^ 54) := by ring
    rw [e, lor_add _ (b1 z)]
  have a01 : ∀ x y : ℕ, 2 ^ 108 * (x % 2 ^ 54) + 2 ^ 54 * (y % 2 ^ 54) < 2 ^ 1024 := fun x y => by
    have := b1 x
    have := b1 y
    have h1 : 2 ^ 108 * (x % 2 ^ 54) ≤ 2 ^ 108 * (2 ^ 54 - 1) := Nat.mul_le_mul_left _ (by omega)
    have h2 : 2 ^ 54 * (y % 2 ^ 54) ≤ 2 ^ 54 * (2 ^ 54 - 1) := Nat.mul_le_mul_left _ (by omega)
    have h3 : 2 ^ 108 * (2 ^ 54 - 1) + 2 ^ 54 * (2 ^ 54 - 1) < 2 ^ 1024 := by norm_num
    omega
  rw [c01, c01, lor_split _ _ (a01 _ _) (a2 _), c2, c2]

theorem red_lane : ∀ x < 145, 205 * x / 2 ^ 10 = x / 5 := by decide

theorem LANE_lt : LANE < 2 ^ 162 := by unfold LANE; decide

theorem redP_eq {c c' : Fin 3 → Fin 3 → ℕ} (hc : ∀ r j, c r j < 145) (hc' : ∀ r j, c' r j < 145) :
    redP (packB c + 2 ^ 1024 * packB c') =
      packB (fun r j => c r j % 5) + 2 ^ 1024 * packB (fun r j => c' r j % 5) := by
  have hmap : ∀ (f : ℕ → ℕ), f 0 = 0 → ∀ (F : Fin 3 → Fin 3 → ℕ) (m : ℕ),
      lanesB (fun r j => f (F r j)) m = f (lanesB F m) := by
    intro f hf F m
    unfold lanesB
    rcases m with _ | _ | _ | _ | _ | _ | _ | _ | _ | m <;> simp [hf]
  have hpk : ∀ (f : ℕ → ℕ), f 0 = 0 → ∀ F : Fin 3 → Fin 3 → ℕ,
      packB (fun r j => f (F r j)) = ev (fun m => f (lanesB F m)) 9 := fun f hf F => by
    unfold packB
    exact ev_congr fun m _ => hmap f hf F m
  have h205 : ∀ F : Fin 3 → Fin 3 → ℕ, 205 * packB F = ev (fun m => 205 * lanesB F m) 9 :=
    fun F => (ev_mul 205 (lanesB F)).symm
  have hdm : ∀ F : Fin 3 → Fin 3 → ℕ,
      packB F = packB (fun r j => F r j % 5) + 5 * packB (fun r j => F r j / 5) := fun F => by
    rw [hpk (· % 5) rfl, hpk (· / 5) rfl, ← ev_mul, ← ev_add]
    unfold packB
    exact ev_congr fun m _ => (Nat.mod_add_div _ _).symm
  have hq : ∀ F : Fin 3 → Fin 3 → ℕ, (∀ r j, F r j < 145) →
      205 * packB F / 2 ^ 10 &&& LANE = packB (fun r j => F r j / 5) := fun F hF => by
    have hl : ∀ m, lanesB F m < 145 := lanesB_lt hF (by norm_num)
    rw [h205, LANE, ev_div_land fun m _ => by have := hl m; omega, hpk (· / 5) rfl]
    exact ev_congr fun m _ => red_lane _ (hl m)
  have hlt : ∀ F : Fin 3 → Fin 3 → ℕ, (∀ r j, F r j < 145) → 205 * packB F < 2 ^ 170 := fun F hF => by
    have : packB F < 2 ^ 162 := packB_lt fun r j => by have := hF r j; omega
    calc 205 * packB F < 2 ^ 8 * 2 ^ 162 := by omega
      _ = 2 ^ 170 := by norm_num
  set P := 205 * packB c
  set Q := 205 * packB c'
  have hP := hlt c hc
  have hP' : P < 2 ^ 1024 := lt_trans hP (by norm_num)
  have ex : (packB c + 2 ^ 1024 * packB c') * 205 = P + 2 ^ 1024 * Q := by ring
  have ediv : (P + 2 ^ 1024 * Q) / 2 ^ 10 = P / 2 ^ 10 + 2 ^ 162 * (2 ^ 852 * Q) := by
    have e : 2 ^ 1024 * Q = 2 ^ 10 * (2 ^ 162 * (2 ^ 852 * Q)) := by ring
    rw [e, Nat.add_mul_div_left _ _ (by positivity)]
  have hP10 : P / 2 ^ 10 < 2 ^ 162 := by omega
  have hLANE := LANE_lt
  have e1 : (P + 2 ^ 1024 * Q) / 2 ^ 10 % 2 ^ 1024 &&& LANE = P / 2 ^ 10 &&& LANE := by
    have h0 : LANE = LANE + 2 ^ 162 * 0 := by ring
    rw [h0, land_split _ _ _ _ hLANE, land_split _ _ _ _ hLANE, Nat.and_zero, Nat.and_zero,
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by norm_num)), ediv, split_mod hP10,
      Nat.mod_eq_of_lt hP10]
  have e2 : (P + 2 ^ 1024 * Q) / 2 ^ 10 / 2 ^ 1024 = Q / 2 ^ 10 := by
    rw [Nat.div_div_eq_div_mul _ (2 ^ 10) (2 ^ 1024), Nat.mul_comm (2 ^ 10) (2 ^ 1024),
      ← Nat.div_div_eq_div_mul, split_div hP']
  unfold redP
  rw [ex, land_split _ _ _ _ (lt_trans hLANE (by norm_num)), e1, e2, hq c hc, hq c' hc']
  rw [hdm c, hdm c']
  omega

@[expose] def fst (x : F25) : ZMod 5 := (x : ZMod 5 × ZMod 5).1

@[expose] def snd (x : F25) : ZMod 5 := (x : ZMod 5 × ZMod 5).2

theorem fst_add (x y : F25) : fst (x + y) = fst x + fst y := rfl

theorem snd_add (x y : F25) : snd (x + y) = snd x + snd y := rfl

theorem fst_mul (x y : F25) : fst (x * y) = fst x * fst y + 2 * snd x * snd y := rfl

theorem snd_mul (x y : F25) : snd (x * y) = fst x * snd y + snd x * fst y := rfl

theorem re_eq (x : F25) : re x = (fst x).val := rfl

theorem im_eq (x : F25) : im x = (snd x).val := rfl

theorem re_mul_apply (X Y : Matrix (Fin 3) (Fin 3) F25) (i j : Fin 3) :
    re ((X * Y) i j) = (re (X i 0) * re (Y 0 j) + 2 * im (X i 0) * im (Y 0 j) +
      (re (X i 1) * re (Y 1 j) + 2 * im (X i 1) * im (Y 1 j)) +
      (re (X i 2) * re (Y 2 j) + 2 * im (X i 2) * im (Y 2 j))) % 5 := by
  rw [← ZMod.val_natCast, re_eq, Matrix.mul_apply, Fin.sum_univ_three]
  congr 1
  simp only [fst_add, fst_mul, re_eq, im_eq]
  push_cast
  simp only [ZMod.natCast_val, ZMod.cast_id', id]

theorem im_mul_apply (X Y : Matrix (Fin 3) (Fin 3) F25) (i j : Fin 3) :
    im ((X * Y) i j) = (re (X i 0) * im (Y 0 j) + im (X i 0) * re (Y 0 j) +
      (re (X i 1) * im (Y 1 j) + im (X i 1) * re (Y 1 j)) +
      (re (X i 2) * im (Y 2 j) + im (X i 2) * re (Y 2 j))) % 5 := by
  rw [← ZMod.val_natCast, im_eq, Matrix.mul_apply, Fin.sum_univ_three]
  congr 1
  simp only [snd_add, snd_mul, re_eq, im_eq]
  push_cast
  simp only [ZMod.natCast_val, ZMod.cast_id', id]

theorem lanesA_zero (F : Fin 3 → Fin 3 → ℕ) : ∀ a, 37 ≤ a → lanesA F a = 0 := fun a ha => by
  unfold lanesA
  rw [List.getD_eq_default]
  simp only [List.length_cons, List.length_nil]
  omega

theorem lanesB_zero (F : Fin 3 → Fin 3 → ℕ) : ∀ a, 9 ≤ a → lanesB F a = 0 := fun a ha => by
  unfold lanesB
  rw [List.getD_eq_default]
  simp only [List.length_cons, List.length_nil]
  omega

theorem lanesA_le {F : Fin 3 → Fin 3 → ℕ} (hF : ∀ i k, F i k < 5) (m : ℕ) : lanesA F m ≤ 4 := by
  have h : ∀ i k, F i k ≤ 4 := fun i k => by have := hF i k; omega
  unfold lanesA
  rcases m with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
    _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | m <;> simp [h]

theorem lanesB_le {F : Fin 3 → Fin 3 → ℕ} (hF : ∀ i k, F i k < 5) (m : ℕ) : lanesB F m ≤ 4 := by
  have := lanesB_lt hF (by norm_num) m
  omega

theorem cv_lane (F G : Fin 3 → Fin 3 → ℕ) (i j : Fin 3) (ℓ : ℕ) (hℓ : ℓ = 15 * i.val + 6 + j.val) :
    cv (lanesA F) (lanesB G) ℓ = F i 0 * G 0 j + F i 1 * G 1 j + F i 2 * G 2 j := by
  subst hℓ
  fin_cases i <;> fin_cases j <;>
    simp [cv, Finset.sum_range_succ, lanesA, lanesB] <;> ring

theorem quad_le : ∀ x < 5, ∀ y < 5, ∀ z < 5, ∀ w < 5, x * y + 2 * z * w ≤ 48 := by decide

theorem quad_le' : ∀ x < 5, ∀ y < 5, ∀ z < 5, ∀ w < 5, x * y + z * w ≤ 48 := by decide

@[expose] def uR (a b c d : Fin 3 → Fin 3 → ℕ) (i j : Fin 3) : ℕ :=
  a i 0 * c 0 j + 2 * b i 0 * d 0 j + (a i 1 * c 1 j + 2 * b i 1 * d 1 j) +
    (a i 2 * c 2 j + 2 * b i 2 * d 2 j)

@[expose] def uI (a b c d : Fin 3 → Fin 3 → ℕ) (i j : Fin 3) : ℕ :=
  a i 0 * d 0 j + b i 0 * c 0 j + (a i 1 * d 1 j + b i 1 * c 1 j) + (a i 2 * d 2 j + b i 2 * c 2 j)

theorem mulP_lanes {a b c d : Fin 3 → Fin 3 → ℕ} (ha5 : ∀ i k, a i k < 5) (hb5 : ∀ i k, b i k < 5)
    (hc5 : ∀ i k, c i k < 5) (hd5 : ∀ i k, d i k < 5) :
    mulP (packA a + 2 ^ 1024 * packA b) (packB c + 2 ^ 1024 * packB d) =
      packB (fun i j => uR a b c d i j % 5) + 2 ^ 1024 * packB (fun i j => uI a b c d i j % 5) := by
  have hp : ∀ F G : Fin 3 → Fin 3 → ℕ,
      packA F * packB G = ev (cv (lanesA F) (lanesB G)) 46 := fun F G =>
    ev_mul_ev (lanesB_zero G) (lanesA_zero F)
  have hcv : ∀ F G : Fin 3 → Fin 3 → ℕ, (∀ i k, F i k < 5) → (∀ i k, G i k < 5) →
      ∀ ℓ < 46, cv (lanesA F) (lanesB G) ℓ ≤ 736 := fun F G hF hG ℓ hℓ => by
    have := cv_le (lanesA_le hF) (lanesB_le hG) ℓ
    have h2 : (ℓ + 1) * (4 * 4) ≤ 46 * 16 := Nat.mul_le_mul (by omega) le_rfl
    omega
  have hDrB : ∀ ℓ < 46, cv (lanesA a) (lanesB c) ℓ + 2 * cv (lanesA b) (lanesB d) ℓ < 2 ^ 18 :=
    fun ℓ hℓ => by
      have := hcv a c ha5 hc5 ℓ hℓ
      have := hcv b d hb5 hd5 ℓ hℓ
      omega
  have hDiB : ∀ ℓ < 46, cv (lanesA a) (lanesB d) ℓ + cv (lanesA b) (lanesB c) ℓ < 2 ^ 18 :=
    fun ℓ hℓ => by
      have := hcv a d ha5 hd5 ℓ hℓ
      have := hcv b c hb5 hc5 ℓ hℓ
      omega
  have eR : packA a * packB c + 2 * (packA b * packB d) =
      ev (fun ℓ => cv (lanesA a) (lanesB c) ℓ + 2 * cv (lanesA b) (lanesB d) ℓ) 46 := by
    rw [hp, hp, ev_add, ev_mul]
  have eI : packA a * packB d + packA b * packB c =
      ev (fun ℓ => cv (lanesA a) (lanesB d) ℓ + cv (lanesA b) (lanesB c) ℓ) 46 := by
    rw [hp, hp, ev_add]
  have hR := lt_trans (ev_lt hDrB) (by norm_num : 2 ^ (18 * 46) < 2 ^ 1024)
  have hI := lt_trans (ev_lt hDiB) (by norm_num : 2 ^ (18 * 46) < 2 ^ 1024)
  have hP0 : packA a * packB c < 2 ^ 1024 := by
    have h := hR
    rw [← eR] at h
    omega
  have ey : (packA a + 2 ^ 1024 * packA b) * (packB c + 2 ^ 1024 * packB d) =
      packA a * packB c + 2 ^ 1024 * (packA a * packB d + packA b * packB c) +
        2 ^ 2048 * (packA b * packB d) := by
    ring
  unfold mulP
  have hI' : packA a * packB d + packA b * packB c < 2 ^ 1024 := by
    rw [eI]
    exact hI
  rw [ey, foldP_eq _ hP0 hI', eR, eI, gatherP_eq _ hR]
  rw [ev_window 6 hDrB (by norm_num) (by norm_num), ev_window 21 hDrB (by norm_num) (by norm_num),
    ev_window 36 hDrB (by norm_num) (by norm_num), ev_window 6 hDiB (by norm_num) (by norm_num),
    ev_window 21 hDiB (by norm_num) (by norm_num), ev_window 36 hDiB (by norm_num) (by norm_num)]
  have hl : ∀ (F G : Fin 3 → Fin 3 → ℕ) (i j : Fin 3) (ℓ : ℕ), ℓ = 15 * i.val + 6 + j.val →
      cv (lanesA F) (lanesB G) ℓ = F i 0 * G 0 j + F i 1 * G 1 j + F i 2 * G 2 j :=
    fun F G i j ℓ hℓ => cv_lane F G i j ℓ hℓ
  simp only [hl a c 0 0 6 rfl, hl b d 0 0 6 rfl, hl a d 0 0 6 rfl, hl b c 0 0 6 rfl,
    hl a c 0 1 (6 + 1) rfl, hl b d 0 1 (6 + 1) rfl, hl a d 0 1 (6 + 1) rfl, hl b c 0 1 (6 + 1) rfl,
    hl a c 0 2 (6 + 2) rfl, hl b d 0 2 (6 + 2) rfl, hl a d 0 2 (6 + 2) rfl, hl b c 0 2 (6 + 2) rfl,
    hl a c 1 0 21 rfl, hl b d 1 0 21 rfl, hl a d 1 0 21 rfl, hl b c 1 0 21 rfl,
    hl a c 1 1 (21 + 1) rfl, hl b d 1 1 (21 + 1) rfl, hl a d 1 1 (21 + 1) rfl,
    hl b c 1 1 (21 + 1) rfl,
    hl a c 1 2 (21 + 2) rfl, hl b d 1 2 (21 + 2) rfl, hl a d 1 2 (21 + 2) rfl,
    hl b c 1 2 (21 + 2) rfl,
    hl a c 2 0 36 rfl, hl b d 2 0 36 rfl, hl a d 2 0 36 rfl, hl b c 2 0 36 rfl,
    hl a c 2 1 (36 + 1) rfl, hl b d 2 1 (36 + 1) rfl, hl a d 2 1 (36 + 1) rfl,
    hl b c 2 1 (36 + 1) rfl,
    hl a c 2 2 (36 + 2) rfl, hl b d 2 2 (36 + 2) rfl, hl a d 2 2 (36 + 2) rfl,
    hl b c 2 2 (36 + 2) rfl]
  have hU5 : ∀ i j, uR a b c d i j < 145 := fun i j => by
    have h0 := quad_le _ (ha5 i 0) _ (hc5 0 j) _ (hb5 i 0) _ (hd5 0 j)
    have h1 := quad_le _ (ha5 i 1) _ (hc5 1 j) _ (hb5 i 1) _ (hd5 1 j)
    have h2 := quad_le _ (ha5 i 2) _ (hc5 2 j) _ (hb5 i 2) _ (hd5 2 j)
    unfold uR
    omega
  have hV5 : ∀ i j, uI a b c d i j < 145 := fun i j => by
    have h0 := quad_le' _ (ha5 i 0) _ (hd5 0 j) _ (hb5 i 0) _ (hc5 0 j)
    have h1 := quad_le' _ (ha5 i 1) _ (hd5 1 j) _ (hb5 i 1) _ (hc5 1 j)
    have h2 := quad_le' _ (ha5 i 2) _ (hd5 2 j) _ (hb5 i 2) _ (hc5 2 j)
    unfold uI
    omega
  rw [← redP_eq hU5 hV5, packB_eq, packB_eq]
  refine congrArg redP ?_
  simp only [uR, uI]
  ring

theorem mulP_enc (X Y : Matrix (Fin 3) (Fin 3) F25) : mulP (encA X) (encB Y) = encB (X * Y) := by
  unfold encA encB
  refine (mulP_lanes (a := fun r j => re (X r j)) (b := fun r j => im (X r j))
    (c := fun r j => re (Y r j)) (d := fun r j => im (Y r j))
    (fun _ _ => re_lt _) (fun _ _ => im_lt _) (fun _ _ => re_lt _) (fun _ _ => im_lt _)).trans ?_
  have e1 : (fun i j => uR (fun r j => re (X r j)) (fun r j => im (X r j)) (fun r j => re (Y r j))
      (fun r j => im (Y r j)) i j % 5) = fun i j => re ((X * Y) i j) := by
    funext i j
    rw [re_mul_apply]
    rfl
  have e2 : (fun i j => uI (fun r j => re (X r j)) (fun r j => im (X r j)) (fun r j => re (Y r j))
      (fun r j => im (Y r j)) i j % 5) = fun i j => im ((X * Y) i j) := by
    funext i j
    rw [im_mul_apply]
    rfl
  rw [e1, e2]

end CFSG.Certificates.U35Pk
