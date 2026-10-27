module

public import Certificates.Data.Kernel.Misc.F7Mat
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.Field.ZMod

set_option exponentiation.threshold 4096

public section

namespace CFSG.KC.Misc.F7

open CFSG.KC.Loop Finset Matrix

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by decide⟩

@[expose] def laneV (x k : ℕ) : ℕ := x / 2 ^ (32 * k) % 2 ^ 32

@[expose] def D (n : ℕ) (c : ℕ → ℕ) : ℕ := ∑ k ∈ range n, c k * 2 ^ (32 * k)

theorem laneV_lt (x k : ℕ) : laneV x k < 2 ^ 32 := Nat.mod_lt _ (by norm_num)

theorem testBit_laneV (x i t : ℕ) (ht : t < 32) :
    (laneV x i).testBit t = x.testBit (t + 32 * i) := by
  rw [laneV, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [ht]

theorem eq_of_testBit_lt {a b : ℕ} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (h : ∀ t < 32, a.testBit t = b.testBit t) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < 32
  · exact h t ht
  · have hle : 2 ^ 32 ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hle), Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hb hle)]

theorem laneV_ext {x y : ℕ} (h : ∀ i, laneV x i = laneV y i) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro j
  have hj : j = j % 32 + 32 * (j / 32) := by omega
  rw [hj, ← testBit_laneV x _ _ (Nat.mod_lt _ (by norm_num)),
    ← testBit_laneV y _ _ (Nat.mod_lt _ (by norm_num)), h]

theorem laneV_and (x y i : ℕ) : laneV (x &&& y) i = laneV x i &&& laneV y i := by
  apply eq_of_testBit_lt (laneV_lt _ _) (Nat.and_lt_two_pow _ (laneV_lt _ _))
  intro t ht
  rw [testBit_laneV _ _ _ ht, Nat.testBit_and, Nat.testBit_and, testBit_laneV _ _ _ ht,
    testBit_laneV _ _ _ ht]

theorem laneV_of_le {x i k : ℕ} (hx : x < 2 ^ (32 * k)) (h : k ≤ i) : laneV x i = 0 := by
  rw [laneV, Nat.div_eq_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))),
    Nat.zero_mod]

theorem laneV_shift15 (y i : ℕ) : laneV (y >>> 15) i % 2 ^ 8 = laneV y i / 2 ^ 15 % 2 ^ 8 := by
  rw [laneV, laneV, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, Nat.mul_comm (2 ^ 15),
    ← Nat.div_div_eq_div_mul]
  generalize y / 2 ^ (32 * i) = w
  have h1 : (2 : ℕ) ^ 15 = 32768 := by norm_num
  have h2 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
  have h3 : (2 : ℕ) ^ 8 = 256 := by norm_num
  rw [h1, h2, h3]
  omega

theorem D_succ (n : ℕ) (c : ℕ → ℕ) : D (n + 1) c = D n c + c n * 2 ^ (32 * n) :=
  sum_range_succ _ _

theorem D_congr {n : ℕ} {c d : ℕ → ℕ} (h : ∀ k < n, c k = d k) : D n c = D n d :=
  sum_congr rfl fun k hk => by rw [h k (mem_range.1 hk)]

theorem D_lt {n : ℕ} {c : ℕ → ℕ} (hc : ∀ k < n, c k < 2 ^ 32) : D n c < 2 ^ (32 * n) := by
  induction n with
  | zero => simp [D]
  | succ n ih =>
    rw [D_succ]
    have h1 := ih fun k hk => hc k (by omega)
    have h2 : c n * 2 ^ (32 * n) ≤ (2 ^ 32 - 1) * 2 ^ (32 * n) :=
      Nat.mul_le_mul_right _ (by have := hc n (by omega); omega)
    have h3 : 2 ^ (32 * (n + 1)) = 2 ^ 32 * 2 ^ (32 * n) := by
      rw [Nat.mul_succ, pow_add, mul_comm]
    have h4 : (2 ^ 32 - 1) * 2 ^ (32 * n) + 2 ^ (32 * n) = 2 ^ 32 * 2 ^ (32 * n) := by
      rw [← Nat.succ_mul]
      norm_num
    omega

theorem lane_D {n : ℕ} {c : ℕ → ℕ} (hc : ∀ k < n, c k < 2 ^ 32) (k : ℕ) :
    laneV (D n c) k = if k < n then c k else 0 := by
  induction n with
  | zero => simp [D, laneV]
  | succ n ih =>
    have hc' : ∀ k < n, c k < 2 ^ 32 := fun k hk => hc k (by omega)
    have hlt := D_lt hc'
    have ih' := ih hc'
    rw [laneV] at ih'
    rw [D_succ, laneV]
    rcases lt_trichotomy k n with h | h | h
    · have e : c n * 2 ^ (32 * n) = c n * 2 ^ (32 * (n - k - 1)) * 2 ^ 32 * 2 ^ (32 * k) := by
        have h32 : 32 * n = 32 * (n - k - 1) + 32 + 32 * k := by omega
        rw [h32, pow_add, pow_add]
        ring
      rw [e, Nat.add_mul_div_right _ _ (by positivity), Nat.add_mul_mod_self_right, ih',
        ite_eq_left h, ite_eq_left (by omega)]
    · rw [h, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlt, Nat.zero_add,
        Nat.mod_eq_of_lt (hc _ (by omega)), ite_eq_left (by omega)]
    · have hx : D n c + c n * 2 ^ (32 * n) < 2 ^ (32 * k) := by
        have := D_lt hc
        rw [D_succ] at this
        exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [Nat.div_eq_of_lt hx, Nat.zero_mod, ite_eq_right (by omega)]

theorem eq_D {x n : ℕ} (hx : x < 2 ^ (32 * n)) : x = D n (laneV x) := by
  apply laneV_ext
  intro k
  rw [lane_D (fun k _ => laneV_lt x k)]
  split_ifs with h
  · rfl
  · exact laneV_of_le hx (by omega)

theorem D_add (n : ℕ) (c d : ℕ → ℕ) : D n c + D n d = D n fun k => c k + d k := by
  rw [D, D, D, ← sum_add_distrib]
  exact sum_congr rfl fun k _ => (add_mul _ _ _).symm

theorem D_mul (n a : ℕ) (c : ℕ → ℕ) : a * D n c = D n fun k => a * c k := by
  rw [D, D, mul_sum]
  exact sum_congr rfl fun k _ => (mul_assoc _ _ _).symm

theorem D_mul_right (n a : ℕ) (c : ℕ → ℕ) : D n c * a = D n fun k => c k * a := by
  rw [mul_comm, D_mul]
  exact D_congr fun k _ => mul_comm _ _

theorem D_add_len (a b : ℕ) (c : ℕ → ℕ) :
    D (a + b) c = D a c + D b (fun j => c (a + j)) * 2 ^ (32 * a) := by
  rw [D, sum_range_add, D, D, sum_mul]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [mul_add, pow_add]
  ring

theorem D_blocks (m : ℕ) (c : ℕ → ℕ) :
    D (45 * m) c = ∑ i ∈ range m, D 45 (fun j => c (45 * i + j)) * 2 ^ (1440 * i) := by
  induction m with
  | zero => simp [D]
  | succ m ih =>
    have e : 32 * (45 * m) = 1440 * m := by ring
    rw [Nat.mul_succ, D_add_len, ih, sum_range_succ, e]

theorem D_zero (n : ℕ) : D n (fun _ => 0) = 0 := by simp [D]

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

theorem bAnd_eq {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> simp [andB]

theorem nIf_eq (b : Bool) (t e : ℕ) : ifN b t e = if b = true then t else e := by
  cases b <;> rfl

theorem bIf_true_eq {c e : Bool} : ifB c true e = true ↔ c = true ∨ e = true := by
  cases c <;> simp [ifB]

theorem bNot_eq {a : Bool} : notB a = true ↔ a = false := by
  cases a <;> simp [notB]

theorem sumN_eq (n : ℕ) (f : ℕ → ℕ) : sumN n f = ∑ k ∈ range n, f k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum_range_succ, ← ih]
    rfl

theorem allN_iff (n : ℕ) (f : ℕ → Bool) : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    change andB (f n) (allN n f) = true ↔ _
    rw [bAnd_eq, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · exact h2 i h
      · rw [h]
        exact h1
    · intro h
      exact ⟨h n (by omega), fun i hi => h i (by omega)⟩

theorem lane_eq (r j : ℕ) : lane r j = laneV r j := by
  have h : (4294967295 : ℕ) = 2 ^ 32 - 1 := by norm_num
  change (r >>> (32 * j)) &&& 4294967295 = _
  rw [h, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, laneV]

theorem rowMask_eq : rowMask = 2 ^ 1440 - 1 := by
  change (1 <<< 1440) - 1 = _
  rw [Nat.shiftLeft_eq, one_mul]

theorem row_eq (A i : ℕ) : row A i = A / 2 ^ (1440 * i) % 2 ^ 1440 := by
  change (A >>> (1440 * i)) &&& rowMask = _
  rw [rowMask_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem row_lt (A i : ℕ) : row A i < 2 ^ (32 * 45) := by
  rw [row_eq]
  exact Nat.mod_lt _ (by positivity)

theorem laneV_row {A i j : ℕ} (hj : j < 45) : laneV (row A i) j = laneV A (45 * i + j) := by
  apply eq_of_testBit_lt (laneV_lt _ _) (laneV_lt _ _)
  intro t ht
  rw [testBit_laneV _ _ _ ht, testBit_laneV _ _ _ ht, row_eq, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, decide_eq_true (by omega : t + 32 * j < 1440), Bool.true_and]
  congr 1
  ring

theorem m8_eq : m8 = D 45 fun _ => 255 := by
  rw [m8, sumN_eq, D]
  refine sum_congr rfl fun j _ => ?_
  change 255 <<< (32 * j) = _
  rw [Nat.shiftLeft_eq]

theorem red7_eq (v : ℕ) : red7 v = v - 7 * (((v * 4682) >>> 15) &&& m8) := rfl

theorem red7_D {n : ℕ} {c : ℕ → ℕ} (hn : n ≤ 45) (hc : ∀ k < n, c k < 1621) :
    red7 (D n c) = D n fun k => c k % 7 := by
  have p32 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
  have hm : ∀ i, laneV m8 i = if i < 45 then 255 else 0 := fun i => by
    rw [m8_eq, lane_D (n := 45) (c := fun _ => 255) (fun _ _ => by norm_num)]
  have hy : ∀ i, laneV (D n c * 4682) i = if i < n then c i * 4682 else 0 := fun i => by
    rw [D_mul_right, lane_D (n := n) (c := fun k => c k * 4682)
      (fun k hk => by have := hc k hk; rw [p32]; omega)]
  have hq : ((D n c * 4682) >>> 15) &&& m8 = D n fun k => c k / 7 := by
    apply laneV_ext
    intro i
    rw [laneV_and, hm, lane_D (n := n) (c := fun k => c k / 7)
      (fun k hk => by have := hc k hk; rw [p32]; omega)]
    by_cases h45 : i < 45
    · have h255 : (255 : ℕ) = 2 ^ 8 - 1 := by norm_num
      rw [ite_eq_left h45, h255, Nat.and_two_pow_sub_one_eq_mod, laneV_shift15, hy]
      by_cases hi : i < n
      · rw [ite_eq_left hi, ite_eq_left hi]
        have := hc i hi
        have h1 : (2 : ℕ) ^ 15 = 32768 := by norm_num
        have h2 : (2 : ℕ) ^ 8 = 256 := by norm_num
        rw [h1, h2]
        have hq7 : c i * 4682 / 32768 = c i / 7 := by omega
        rw [hq7]
        exact Nat.mod_eq_of_lt (by omega)
      · rw [ite_eq_right hi, ite_eq_right hi]
        rfl
    · rw [ite_eq_right h45, Nat.and_zero, ite_eq_right (by omega)]
  have e : D n c = (D n fun k => c k % 7) + 7 * D n fun k => c k / 7 := by
    rw [D_mul, D_add]
    exact D_congr fun k _ => (Nat.mod_add_div _ _).symm
  rw [red7_eq, hq]
  omega

@[expose] def ent {m : ℕ} (A : Matrix (Fin m) (Fin 45) (ZMod 7)) (i j : ℕ) : ℕ :=
  if h : i < m ∧ j < 45 then (A ⟨i, h.1⟩ ⟨j, h.2⟩).val else 0

@[expose] def ev (v : Fin 45 → ZMod 7) (j : ℕ) : ℕ := if h : j < 45 then (v ⟨j, h⟩).val else 0

@[expose] def enc {m : ℕ} (A : Matrix (Fin m) (Fin 45) (ZMod 7)) : ℕ :=
  D (45 * m) fun k => ent A (k / 45) (k % 45)

@[expose] def encV (v : Fin 45 → ZMod 7) : ℕ := D 45 (ev v)

@[expose] def rows {m : ℕ} (V : Matrix (Fin m) (Fin 45) (ZMod 7)) : Fin m → Fin 45 → ZMod 7 :=
  fun i => V i

theorem ent_lt {m : ℕ} (A : Matrix (Fin m) (Fin 45) (ZMod 7)) (i j : ℕ) : ent A i j < 7 := by
  rw [ent]
  split_ifs
  · exact ZMod.val_lt _
  · norm_num

theorem ev_lt (v : Fin 45 → ZMod 7) (j : ℕ) : ev v j < 7 := by
  rw [ev]
  split_ifs
  · exact ZMod.val_lt _
  · norm_num

theorem ev_row {m : ℕ} (A : Matrix (Fin m) (Fin 45) (ZMod 7)) {i : ℕ} (hi : i < m) (j : ℕ) :
    ev (rows A ⟨i, hi⟩) j = ent A i j := by
  by_cases hj : j < 45 <;> simp [ev, ent, rows, hi, hj]

theorem ent_pos {m : ℕ} (A : Matrix (Fin m) (Fin 45) (ZMod 7)) {k : ℕ} (hk : k < 45 * m) :
    ent A (k / 45) (k % 45) = (A ⟨k / 45, by omega⟩ ⟨k % 45, by omega⟩).val := by
  rw [ent, dite_eq_left ⟨by omega, by omega⟩]

theorem ent_lt32 {m : ℕ} (A : Matrix (Fin m) (Fin 45) (ZMod 7)) :
    ∀ k < 45 * m, ent A (k / 45) (k % 45) < 2 ^ 32 :=
  fun k _ => lt_trans (ent_lt A _ _) (by norm_num)

theorem ev_lt32 (v : Fin 45 → ZMod 7) : ∀ k < 45, ev v k < 2 ^ 32 :=
  fun k _ => lt_trans (ev_lt v k) (by norm_num)

theorem laneV_encV (v : Fin 45 → ZMod 7) (j : Fin 45) : laneV (encV v) j = (v j).val := by
  rw [encV, lane_D (ev_lt32 v), ite_eq_left j.isLt, ev, dite_eq_left j.isLt]

theorem lane_encV (v : Fin 45 → ZMod 7) (j : ℕ) : lane (encV v) j = ev v j := by
  rw [lane_eq, encV, lane_D (ev_lt32 v)]
  by_cases hj : j < 45
  · rw [ite_eq_left hj]
  · rw [ite_eq_right hj, ev, dite_eq_right hj]

theorem enc_lt {m : ℕ} (A : Matrix (Fin m) (Fin 45) (ZMod 7)) : enc A < 2 ^ (32 * (45 * m)) :=
  D_lt (ent_lt32 A)

theorem encV_lt (v : Fin 45 → ZMod 7) : encV v < 2 ^ (32 * 45) := D_lt (ev_lt32 v)

theorem encV_inj {u v : Fin 45 → ZMod 7} (h : encV u = encV v) : u = v := by
  funext j
  have h1 := congrArg (fun x => laneV x j) h
  simp only [laneV_encV] at h1
  exact ZMod.val_injective _ h1

theorem encV_zero : encV 0 = 0 := by
  rw [encV, ← D_zero 45]
  exact D_congr fun k hk => by simp [ev, hk]

theorem enc_inj {m : ℕ} {A B : Matrix (Fin m) (Fin 45) (ZMod 7)} (h : enc A = enc B) : A = B := by
  ext i j
  have hk : 45 * (i : ℕ) + j < 45 * m := by omega
  have h1 := congrArg (fun x => laneV x (45 * i + j)) h
  simp only [enc] at h1
  rw [lane_D (ent_lt32 A), lane_D (ent_lt32 B), ite_eq_left hk, ite_eq_left hk, ent_pos A hk,
    ent_pos B hk] at h1
  have e1 : (45 * (i : ℕ) + j) / 45 = i := by omega
  have e2 : (45 * (i : ℕ) + j) % 45 = j := by omega
  simp only [e1, e2] at h1
  exact ZMod.val_injective _ h1

theorem row_enc {m : ℕ} (A : Matrix (Fin m) (Fin 45) (ZMod 7)) (i : Fin m) :
    row (enc A) i = encV (rows A i) := by
  apply laneV_ext
  intro j
  by_cases hj : j < 45
  · have hk : 45 * (i : ℕ) + j < 45 * m := by omega
    rw [laneV_row hj, enc, lane_D (ent_lt32 A), ite_eq_left hk, ent_pos A hk,
      laneV_encV (rows A i) ⟨j, hj⟩]
    have e1 : (45 * (i : ℕ) + j) / 45 = i := by omega
    have e2 : (45 * (i : ℕ) + j) % 45 = j := by omega
    simp only [e1, e2, rows]
  · rw [laneV_of_le (row_lt _ _) (by omega), laneV_of_le (encV_lt _) (by omega)]

theorem rowMul_eq (r B : ℕ) : rowMul r B = red7 (∑ k ∈ range 45, lane r k * row B k) := by
  rw [rowMul, sumN_eq]
  rfl

theorem rowMul_enc (v : Fin 45 → ZMod 7) (B : Matrix (Fin 45) (Fin 45) (ZMod 7)) :
    rowMul (encV v) (enc B) = encV (v ᵥ* B) := by
  have hs : ∑ k ∈ range 45, lane (encV v) k * row (enc B) k =
      D 45 fun j => ∑ k ∈ range 45, ev v k * ent B k j := by
    have h1 : ∀ k ∈ range 45, lane (encV v) k * row (enc B) k =
        ∑ j ∈ range 45, ev v k * ent B k j * 2 ^ (32 * j) := fun k hk => by
      have hk' := mem_range.1 hk
      rw [lane_encV, row_enc B ⟨k, hk'⟩, encV, D_mul, D]
      exact sum_congr rfl fun j _ => by rw [ev_row B hk']
    rw [sum_congr rfl h1, sum_comm, D]
    exact sum_congr rfl fun j _ => (sum_mul _ _ _).symm
  have hb : ∀ j < 45, ∑ k ∈ range 45, ev v k * ent B k j < 1621 := fun j _ => by
    have : ∑ k ∈ range 45, ev v k * ent B k j ≤ ∑ _k ∈ range 45, 36 :=
      sum_le_sum fun k _ => by
        have h1 := ev_lt v k
        have h2 := ent_lt B k j
        have : ev v k * ent B k j ≤ 6 * 6 := Nat.mul_le_mul (by omega) (by omega)
        omega
    simp only [sum_const, card_range, smul_eq_mul] at this
    omega
  rw [rowMul_eq, hs, red7_D le_rfl hb, encV]
  refine D_congr fun j hj => ?_
  have e : ((∑ k ∈ range 45, ev v k * ent B k j : ℕ) : ZMod 7) = (v ᵥ* B) ⟨j, hj⟩ := by
    rw [Nat.cast_sum, ← Fin.sum_univ_eq_sum_range]
    simp only [Matrix.vecMul, dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.cast_mul, ev, dite_eq_left k.isLt, ent, dite_eq_left ⟨k.isLt, hj⟩,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [ev, dite_eq_left hj, ← e, ZMod.val_natCast]

theorem rowsMul_eq (m A B : ℕ) :
    rowsMul m A B = ∑ i ∈ range m, rowMul (row A i) B * 2 ^ (1440 * i) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [sum_range_succ, ← ih]
    change strictN (rowMul (row A m) B) (fun r => rowsMul m A B + r <<< (1440 * m)) = _
    rw [strictN_eq, Nat.shiftLeft_eq]

theorem rowsMul_enc {m : ℕ} (A : Matrix (Fin m) (Fin 45) (ZMod 7))
    (B : Matrix (Fin 45) (Fin 45) (ZMod 7)) : rowsMul m (enc A) (enc B) = enc (A * B) := by
  rw [rowsMul_eq]
  conv_rhs => rw [enc, D_blocks]
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.1 hi
  rw [row_enc A ⟨i, hi'⟩, rowMul_enc, encV]
  refine congrArg (fun x => x * 2 ^ (1440 * i)) (D_congr fun j hj => ?_)
  have e1 : (45 * i + j) / 45 = i := by omega
  have e2 : (45 * i + j) % 45 = j := by omega
  rw [e1, e2]
  simp [ev, ent, rows, hj, hi', Matrix.mul_apply, Matrix.vecMul, dotProduct]

theorem mmul_enc (A B : Matrix (Fin 45) (Fin 45) (ZMod 7)) : mmul (enc A) (enc B) = enc (A * B) :=
  rowsMul_enc A B

theorem imgS_enc (S : Matrix (Fin 8) (Fin 45) (ZMod 7)) (G : Matrix (Fin 45) (Fin 45) (ZMod 7)) :
    imgS (enc S) (enc G) = enc (S * G) :=
  rowsMul_enc S G

theorem idM_eq : idM = enc (1 : Matrix (Fin 45) (Fin 45) (ZMod 7)) := by
  have h1 : idM = ∑ i ∈ range 45, 2 ^ (1472 * i) := by
    rw [idM, sumN_eq]
    refine sum_congr rfl fun i _ => ?_
    change 1 <<< (1472 * i) = _
    rw [Nat.shiftLeft_eq, one_mul]
  rw [h1, enc, D_blocks]
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.1 hi
  have h2 : (D 45 fun j => ent (1 : Matrix (Fin 45) (Fin 45) (ZMod 7)) ((45 * i + j) / 45)
      ((45 * i + j) % 45)) = 2 ^ (32 * i) := by
    rw [D, sum_eq_single i]
    · have e1 : (45 * i + i) / 45 = i := by omega
      have e2 : (45 * i + i) % 45 = i := by omega
      have hv : (1 : ZMod 7).val = 1 := rfl
      rw [e1, e2, ent, dite_eq_left ⟨hi', hi'⟩, Matrix.one_apply_eq, hv, one_mul]
    · intro j hj hji
      have hj' := mem_range.1 hj
      have e1 : (45 * i + j) / 45 = i := by omega
      have e2 : (45 * i + j) % 45 = j := by omega
      rw [e1, e2, ent, dite_eq_left ⟨hi', hj'⟩, Matrix.one_apply_ne (by simp [Fin.ext_iff]; omega),
        ZMod.val_zero, zero_mul]
    · intro h
      exact absurd (mem_range.2 hi') h
  have e3 : 32 * i + 1440 * i = 1472 * i := by ring
  rw [h2, ← pow_add, e3]

theorem powM_enc (A : Matrix (Fin 45) (Fin 45) (ZMod 7)) (e : ℕ) :
    powM (enc A) e = enc (A ^ e) := by
  induction e with
  | zero =>
    rw [pow_zero, ← idM_eq]
    rfl
  | succ e ih =>
    change strictN (mmul (powM (enc A) e) (enc A)) (fun x => x) = _
    rw [strictN_eq, ih, mmul_enc, pow_succ]

@[expose] def decC (m c : ℕ) : Matrix (Fin m) (Fin 45) (ZMod 7) :=
  fun i j => ((c / 2 ^ (3 * (45 * (i : ℕ) + j)) % 8 : ℕ) : ZMod 7)

theorem widenR_eq (m c : ℕ) : widenR m c = enc (decC m c) := by
  rw [widenR, sumN_eq, enc, D_blocks]
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.1 hi
  rw [sumN_eq, D, sum_mul]
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_range.1 hj
  have h7 : (7 : ℕ) = 2 ^ 3 - 1 := by norm_num
  change ((c >>> (3 * (45 * i + j)) &&& 7) % 7) <<< (32 * (45 * i + j)) = _
  have e1 : (45 * i + j) / 45 = i := by omega
  have e2 : (45 * i + j) % 45 = j := by omega
  rw [e1, e2, ent, dite_eq_left ⟨hi', hj'⟩, decC, ZMod.val_natCast, Nat.shiftLeft_eq, h7,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, mul_assoc, ← pow_add]
  congr 2
  ring

theorem widen_eq (c : ℕ) : widen c = enc (decC 45 c) := widenR_eq 45 c

@[expose] def rowSpan {m : ℕ} (V : Matrix (Fin m) (Fin 45) (ZMod 7)) :
    Submodule (ZMod 7) (Fin 45 → ZMod 7) :=
  Submodule.span (ZMod 7) (Set.range (rows V))

def Pivots (V : Matrix (Fin 8) (Fin 45) (ZMod 7)) (p : Fin 8 → Fin 45) : Prop :=
  ∀ c c', rows V c' (p c) = if c' = c then 1 else 0

theorem pivOK_spec {V : Matrix (Fin 8) (Fin 45) (ZMod 7)} {piv : List ℕ}
    (h : pivOK (enc V) piv = true) :
    ∃ p : Fin 8 → Fin 45, (∀ c, (p c : ℕ) = nthF piv c) ∧ Pivots V p := by
  rw [pivOK, allN_iff] at h
  have h1 := h
  have h2 : ∀ c : Fin 8, nthF piv c < 45 := fun c => by
    have := h1 c c.isLt
    rw [bAnd_eq, Nat.blt_eq] at this
    exact this.1
  refine ⟨fun c => ⟨nthF piv c, h2 c⟩, fun c => rfl, fun c c' => ?_⟩
  have h3 := h1 c c.isLt
  rw [bAnd_eq] at h3
  have h4 := (allN_iff _ _).1 h3.2 c' c'.isLt
  rw [Nat.beq_eq, nIf_eq, row_enc V c', lane_encV, ev, dite_eq_left (h2 c)] at h4
  apply ZMod.val_injective
  rw [h4]
  by_cases hc : c' = c
  · rw [ite_eq_left hc]
    rw [ite_eq_left (by rw [hc]; exact Nat.beq_refl _)]
    rfl
  · rw [ite_eq_right hc, ZMod.val_zero]
    rw [ite_eq_right (by rw [Nat.beq_eq]; exact fun h => hc (Fin.ext h))]

theorem mem_rowSpan_iff {V : Matrix (Fin 8) (Fin 45) (ZMod 7)} {p : Fin 8 → Fin 45}
    (hp : Pivots V p) (u : Fin 45 → ZMod 7) : u ∈ rowSpan V ↔ u = ∑ c, u (p c) • rows V c := by
  unfold Pivots at hp
  constructor
  · intro hu
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 7)).1 hu
    refine sum_congr rfl fun c _ => ?_
    congr 1
    simp [Finset.sum_apply, hp]
  · intro hu
    rw [hu]
    exact Submodule.sum_mem _ fun c _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self c))

theorem redRow_enc {V : Matrix (Fin 8) (Fin 45) (ZMod 7)} {piv : List ℕ} {p : Fin 8 → Fin 45}
    (hpv : ∀ c, (p c : ℕ) = nthF piv c) (u : Fin 45 → ZMod 7) :
    redRow (encV u) (enc V) piv = encV (u - ∑ c, u (p c) • rows V c) := by
  have hs : ∑ c ∈ range 8, (7 - lane (encV u) (nthF piv c)) * row (enc V) c =
      D 45 fun j => ∑ c ∈ range 8, (7 - ev u (nthF piv c)) * ent V c j := by
    have h1 : ∀ c ∈ range 8, (7 - lane (encV u) (nthF piv c)) * row (enc V) c =
        ∑ j ∈ range 45, (7 - ev u (nthF piv c)) * ent V c j * 2 ^ (32 * j) := fun c hc => by
      have hc' := mem_range.1 hc
      rw [lane_encV, row_enc V ⟨c, hc'⟩, encV, D_mul, D]
      exact sum_congr rfl fun j _ => by rw [ev_row V hc']
    rw [sum_congr rfl h1, sum_comm, D]
    exact sum_congr rfl fun j _ => (sum_mul _ _ _).symm
  rw [redRow, sumN_eq]
  change red7 (encV u + ∑ c ∈ range 8, (7 - lane (encV u) (nthF piv c)) * row (enc V) c) = _
  have hb : ∀ j < 45, ev u j + ∑ c ∈ range 8, (7 - ev u (nthF piv c)) * ent V c j < 1621 :=
    fun j _ => by
      have : ∑ c ∈ range 8, (7 - ev u (nthF piv c)) * ent V c j ≤ ∑ _c ∈ range 8, 42 :=
        sum_le_sum fun c _ => by
          have h2 := ent_lt V c j
          have : (7 - ev u (nthF piv c)) * ent V c j ≤ 7 * 6 := Nat.mul_le_mul (by omega) (by omega)
          omega
      simp only [sum_const, card_range, smul_eq_mul] at this
      have := ev_lt u j
      omega
  rw [hs, encV, D_add, red7_D le_rfl hb, encV]
  refine D_congr fun j hj => ?_
  conv_rhs => rw [ev, dite_eq_left hj]
  rw [← ZMod.val_natCast]
  congr 1
  push_cast
  rw [Finset.sum_range (fun c => ((7 - ev u (nthF piv c) : ℕ) : ZMod 7) * (ent V c j : ZMod 7))]
  have hc : ∀ c : Fin 8, ((7 - ev u (nthF piv c) : ℕ) : ZMod 7) = -u (p c) := fun c => by
    have h1 := ev_lt u (nthF piv c)
    rw [Nat.cast_sub (by omega), ← hpv c, ev, dite_eq_left (p c).isLt, ZMod.natCast_zmod_val]
    have h7 : ((7 : ℕ) : ZMod 7) = 0 := rfl
    rw [h7, zero_sub]
  simp only [hc]
  simp [ev, ent, rows, hj, Finset.sum_apply, sub_eq_add_neg]

theorem inSpan_iff {U V : Matrix (Fin 8) (Fin 45) (ZMod 7)} {piv : List ℕ}
    (h : pivOK (enc V) piv = true) : inSpan (enc U) (enc V) piv = true ↔ rowSpan U ≤ rowSpan V := by
  obtain ⟨p, hpv, hp⟩ := pivOK_spec h
  rw [rowSpan, Submodule.span_le, Set.range_subset_iff]
  rw [inSpan, allN_iff]
  constructor
  · intro h1 i
    have h2 := h1 i i.isLt
    rw [Nat.beq_eq, row_enc U i, redRow_enc hpv] at h2
    exact (mem_rowSpan_iff hp _).2 (sub_eq_zero.1 (encV_inj (h2.trans encV_zero.symm)))
  · intro h1 i hi
    have h2 := (mem_rowSpan_iff hp _).1 (h1 ⟨i, hi⟩)
    rw [Nat.beq_eq, row_enc U ⟨i, hi⟩, redRow_enc hpv]
    change encV (rows U ⟨i, hi⟩ - _) = 0
    rw [← h2, sub_self, encV_zero]

theorem linearIndependent_of_pivots {V : Matrix (Fin 8) (Fin 45) (ZMod 7)} {p : Fin 8 → Fin 45}
    (hp : Pivots V p) : LinearIndependent (ZMod 7) (rows V) := by
  unfold Pivots at hp
  rw [Fintype.linearIndependent_iff]
  intro g hg c
  have := congrFun hg (p c)
  simpa [Finset.sum_apply, hp] using this

theorem finrank_rowSpan {V : Matrix (Fin 8) (Fin 45) (ZMod 7)} {piv : List ℕ}
    (h : pivOK (enc V) piv = true) : Module.finrank (ZMod 7) (rowSpan V) = 8 := by
  obtain ⟨p, -, hp⟩ := pivOK_spec h
  rw [rowSpan, finrank_span_eq_card (linearIndependent_of_pivots hp), Fintype.card_fin]

theorem rowSpan_mul {m : ℕ} (U : Matrix (Fin m) (Fin 45) (ZMod 7))
    (G : Matrix (Fin 45) (Fin 45) (ZMod 7)) :
    rowSpan (U * G) = (rowSpan U).map G.vecMulLinear := by
  rw [rowSpan, rowSpan, Submodule.map_span, ← Set.range_comp]
  congr 2

theorem rowSpan_mul_eq {U V : Matrix (Fin 8) (Fin 45) (ZMod 7)}
    {G H : Matrix (Fin 45) (Fin 45) (ZMod 7)} {pU pV : List ℕ} (hU : pivOK (enc U) pU = true)
    (hV : pivOK (enc V) pV = true) (hG : G * H = 1)
    (h : inSpan (imgS (enc U) (enc G)) (enc V) pV = true) : rowSpan (U * G) = rowSpan V := by
  rw [imgS_enc, inSpan_iff hV] at h
  refine Submodule.eq_of_le_of_finrank_eq h ?_
  rw [finrank_rowSpan hV]
  obtain ⟨p, -, hp⟩ := pivOK_spec hU
  have hker : LinearMap.ker G.vecMulLinear = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun v hv => ?_
    rw [Matrix.vecMulLinear_apply] at hv
    rw [← Matrix.vecMul_one v, ← hG, ← Matrix.vecMul_vecMul, hv, Matrix.zero_vecMul]
  have e : rows (U * G) = G.vecMulLinear ∘ rows U := by
    funext i
    ext j
    simp [rows, Matrix.mul_apply, Matrix.vecMul, dotProduct]
  have hli : LinearIndependent (ZMod 7) (rows (U * G)) := by
    rw [e]
    exact (linearIndependent_of_pivots hp).map' G.vecMulLinear hker
  rw [rowSpan, finrank_span_eq_card hli, Fintype.card_fin]

theorem rowSpan_ne {U V : Matrix (Fin 8) (Fin 45) (ZMod 7)} {pV : List ℕ}
    (hV : pivOK (enc V) pV = true) (h : inSpan (enc U) (enc V) pV = false) :
    rowSpan U ≠ rowSpan V := by
  intro e
  have := (inSpan_iff hV).2 e.le
  rw [h] at this
  exact Bool.false_ne_true this

end CFSG.KC.Misc.F7

end
