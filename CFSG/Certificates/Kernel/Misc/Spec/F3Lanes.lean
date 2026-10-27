module

public import CFSG.Certificates.Kernel.Misc.Spec.F2Mat
public import CFSG.Certificates.Kernel.Misc.Spec.Words
public import CFSG.Certificates.Kernel.Misc.Spec.ArrMat
import CFSG.Certificates.Kernel.Spor.PK.MiscBase

public section

namespace CFSG.KC.Misc.Spec

@[expose] def lanes (n : ℕ) (g : ℕ → ℕ) : ℕ := ∑ t ∈ Finset.range n, g t * 2 ^ (8 * t)

@[expose] def lane8 (X t : ℕ) : ℕ := X / 2 ^ (8 * t) % 2 ^ 8

theorem lane8_lt (X t : ℕ) : lane8 X t < 256 := by
  have := Nat.mod_lt (X / 2 ^ (8 * t)) (show 0 < 2 ^ 8 by norm_num)
  unfold lane8
  omega

theorem lanes_lt {n : ℕ} {g : ℕ → ℕ} (hg : ∀ t < n, g t < 256) : lanes n g < 2 ^ (8 * n) :=
  blockSum_lt (n := 8) n hg

theorem testBit_lanes {n : ℕ} {g : ℕ → ℕ} (hg : ∀ t < n, g t < 256) (t b : ℕ) (hb : b < 8) :
    (lanes n g).testBit (8 * t + b) = (decide (t < n) && (g t).testBit b) :=
  testBit_blockSum (n := 8) n hg t b hb

theorem lanes_ext {n : ℕ} {g : ℕ → ℕ} {X : ℕ} (hg : ∀ t < n, g t < 256)
    (hX : ∀ t b, b < 8 → X.testBit (8 * t + b) = (decide (t < n) && (g t).testBit b)) :
    X = lanes n g := by
  apply Nat.eq_of_testBit_eq
  intro q
  have hq : q = 8 * (q / 8) + q % 8 := by omega
  rw [hq, hX _ _ (by omega), testBit_lanes hg _ _ (by omega)]

theorem lane8_lanes {n : ℕ} {g : ℕ → ℕ} (hg : ∀ t < n, g t < 256) {t : ℕ} (ht : t < n) :
    lane8 (lanes n g) t = g t := by
  apply Nat.eq_of_testBit_eq
  intro k
  unfold lane8
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hk : k < 8
  · have h := testBit_lanes hg t k hk
    rw [Nat.add_comm k, h]
    simp [hk, ht]
  · have h : g t < 2 ^ k := by
      calc g t < 256 := hg t ht
        _ = 2 ^ 8 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow h]
    simp [hk]

theorem lanes_lane8 {n X : ℕ} (hX : X < 2 ^ (8 * n)) : X = lanes n (lane8 X) := by
  have hg : ∀ t < n, lane8 X t < 256 := fun t _ => lane8_lt X t
  refine lanes_ext hg fun t b hb => ?_
  unfold lane8
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases ht : t < n
  · simp [hb, ht, Nat.add_comm b]
  · have h : X < 2 ^ (8 * t + b) := by
      calc X < 2 ^ (8 * n) := hX
        _ ≤ 2 ^ (8 * t + b) := Nat.pow_le_pow_right (by omega) (by omega)
    simp [ht, Nat.testBit_lt_two_pow h, Nat.add_comm b]

theorem lanes_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ t < n, f t = g t) : lanes n f = lanes n g :=
  Finset.sum_congr rfl fun t ht => by rw [h t (Finset.mem_range.1 ht)]

theorem lanes_add (n : ℕ) (f g : ℕ → ℕ) :
    lanes n f + lanes n g = lanes n (fun t => f t + g t) := by
  unfold lanes
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => (Nat.add_mul _ _ _).symm

theorem lanes_mul (n c : ℕ) (f : ℕ → ℕ) : lanes n f * c = lanes n (fun t => f t * c) := by
  unfold lanes
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun t _ => Nat.mul_right_comm _ _ _

theorem lanes_sub {n : ℕ} {f g : ℕ → ℕ} (h : ∀ t < n, g t ≤ f t) :
    lanes n f - lanes n g = lanes n (fun t => f t - g t) := by
  have e : lanes n g + lanes n (fun t => f t - g t) = lanes n f := by
    rw [lanes_add]
    exact lanes_congr fun t ht => Nat.add_sub_cancel' (h t ht)
  omega

theorem lanes_and {n : ℕ} {f g : ℕ → ℕ} (hf : ∀ t < n, f t < 256) (hg : ∀ t < n, g t < 256) :
    lanes n f &&& lanes n g = lanes n (fun t => f t &&& g t) := by
  have hh : ∀ t < n, f t &&& g t < 256 := fun t ht =>
    Nat.and_lt_two_pow (f t) (show g t < 2 ^ 8 by simpa using hg t ht)
  refine lanes_ext hh fun t b hb => ?_
  rw [Nat.testBit_and, testBit_lanes hf t b hb, testBit_lanes hg t b hb, Nat.testBit_and]
  cases decide (t < n) <;> simp

theorem lanes_or {n : ℕ} {f g : ℕ → ℕ} (hf : ∀ t < n, f t < 256) (hg : ∀ t < n, g t < 256) :
    lanes n f ||| lanes n g = lanes n (fun t => f t ||| g t) := by
  have hh : ∀ t < n, f t ||| g t < 256 := fun t ht =>
    Nat.or_lt_two_pow (show f t < 2 ^ 8 by simpa using hf t ht)
      (show g t < 2 ^ 8 by simpa using hg t ht)
  refine lanes_ext hh fun t b hb => ?_
  rw [Nat.testBit_or, testBit_lanes hf t b hb, testBit_lanes hg t b hb, Nat.testBit_or]
  cases decide (t < n) <;> simp

theorem lanes_shr {n : ℕ} {g : ℕ → ℕ} (hg : ∀ t < n, g t < 256) (k : ℕ) :
    lanes n g >>> (8 * k) = lanes n (fun t => if t + k < n then g (t + k) else 0) := by
  have hh : ∀ t < n, (if t + k < n then g (t + k) else 0) < 256 := by
    intro t _
    split
    · exact hg _ (by assumption)
    · omega
  refine lanes_ext hh fun t b hb => ?_
  rw [Nat.testBit_shiftRight]
  have e : 8 * k + (8 * t + b) = 8 * (t + k) + b := by ring
  rw [e, testBit_lanes hg (t + k) b hb]
  by_cases h : t + k < n
  · have ht : t < n := by omega
    simp [h, ht]
  · simp [h]

theorem testBit_top {y k : ℕ} (hy : y < 2 * 2 ^ k) : y.testBit k = decide (2 ^ k ≤ y) := by
  by_cases h : 2 ^ k ≤ y
  · obtain ⟨r, rfl⟩ : ∃ r, y = 2 ^ k + r := ⟨y - 2 ^ k, by omega⟩
    rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (by omega)]
    simp
  · rw [Nat.testBit_lt_two_pow (by omega)]
    simp [h]

theorem and_top {y k : ℕ} (hy : y < 2 * 2 ^ k) :
    y &&& 2 ^ k = if 2 ^ k ≤ y then 2 ^ k else 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases hj : k = j
  · subst hj
    rw [testBit_top hy]
    by_cases h : 2 ^ k ≤ y <;> simp [h]
  · by_cases h : 2 ^ k ≤ y <;> simp [h, hj]

theorem or_top {a k : ℕ} (ha : a < 2 ^ k) : a ||| 2 ^ k = a + 2 ^ k := by
  have h := Nat.two_pow_add_eq_or_of_lt ha 1
  rw [Nat.mul_one] at h
  rw [Nat.or_comm, ← h, Nat.add_comm]

theorem csub_lanes {n : ℕ} {f : ℕ → ℕ} {c : ℕ} (hf : ∀ t < n, f t < 128) (hc : c ≤ 128) :
    CFSG.KC.Ord.csub 8 (lanes n fun _ => 1) (lanes n fun _ => 128) c (lanes n f) =
      lanes n (fun t => if c ≤ f t then f t - c else f t) := by
  have hf256 : ∀ t < n, f t < 256 := fun t ht => by have := hf t ht; omega
  have h128 : ∀ t < n, (fun _ : ℕ => (128 : ℕ)) t < 256 := fun _ _ => by norm_num
  have e7 : (128 : ℕ) = 2 ^ 7 := by norm_num
  have s1 : lanes n f ||| lanes n (fun _ => 128) = lanes n (fun t => f t + 128) := by
    rw [lanes_or hf256 h128]
    refine lanes_congr fun t ht => ?_
    have h := hf t ht
    rw [e7] at h ⊢
    exact or_top h
  have s2 : c * lanes n (fun _ => 1) = lanes n (fun _ => c) := by
    rw [Nat.mul_comm, lanes_mul]
    exact lanes_congr fun t _ => Nat.one_mul c
  have s3 : lanes n (fun t => f t + 128) - lanes n (fun _ => c) =
      lanes n (fun t => f t + 128 - c) :=
    lanes_sub fun t ht => by have := hf t ht; omega
  have s4 : lanes n (fun t => f t + 128 - c) &&& lanes n (fun _ => 128) =
      lanes n (fun t => (if c ≤ f t then 1 else 0) * 128) := by
    rw [lanes_and (fun t ht => by have := hf t ht; omega) h128]
    refine lanes_congr fun t ht => ?_
    have h := hf t ht
    have a1 := and_top (y := f t + 128 - c) (k := 7) (by omega)
    norm_num at a1
    show (f t + 128 - c) &&& 128 = (if c ≤ f t then 1 else 0) * 128
    rw [a1]
    by_cases hct : c ≤ f t
    · have h1 : 128 ≤ f t + 128 - c := by omega
      simp [hct, h1]
    · have h1 : ¬ 128 ≤ f t + 128 - c := by omega
      simp [hct, h1]
  have s5 : lanes n (fun t => (if c ≤ f t then 1 else 0) * 128) >>> 7 =
      lanes n (fun t => if c ≤ f t then 1 else 0) := by
    rw [← lanes_mul, Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel _ (by norm_num)]
  have s6 : lanes n (fun t => if c ≤ f t then 1 else 0) * c =
      lanes n (fun t => (if c ≤ f t then 1 else 0) * c) := lanes_mul _ _ _
  have s7 : lanes n f - lanes n (fun t => (if c ≤ f t then 1 else 0) * c) =
      lanes n (fun t => f t - (if c ≤ f t then 1 else 0) * c) :=
    lanes_sub fun t _ => by split <;> simp_all
  unfold CFSG.KC.Ord.csub
  show lanes n f - (((lanes n f ||| lanes n (fun _ => 128)) - c * lanes n (fun _ => 1)) &&&
      lanes n (fun _ => 128)) >>> (8 - 1) * c = _
  rw [s1, s2, s3, s4, show 8 - 1 = 7 from rfl, s5, s6, s7]
  exact lanes_congr fun t _ => by split <;> simp_all

@[expose] def cs (c v : ℕ) : ℕ := if c ≤ v then v - c else v

theorem cs_le (c v : ℕ) : cs c v ≤ v := by
  unfold cs
  split <;> omega

@[expose] def r3 (v : ℕ) : ℕ := cs 3 (cs 6 (cs 12 (cs 24 (cs 48 v))))

theorem r3_eq : ∀ v < 96, r3 v = v % 3 := by
  decide

theorem laneOnes_eq : CFSG.KC.Misc.G24.laneOnes = lanes 144 (fun _ => 1) := by
  have h1 : lanes 144 (fun _ => 1) = repu 8 144 := by
    unfold lanes repu
    exact Finset.sum_congr rfl fun t _ => Nat.one_mul _
  have h2 := repu_eq (s := 8) (m := 144) (by norm_num)
  have h3 : (2 : ℕ) ^ (8 * 144) = 2 ^ 1152 := by rw [show 8 * 144 = 1152 from rfl]
  have h4 : (2 : ℕ) ^ 8 - 1 = 255 := by norm_num
  rw [h1, h2, h3, h4]
  unfold CFSG.KC.Misc.G24.laneOnes
  rw [shl1_eq]
  generalize (2 : ℕ) ^ 1152 = N
  rfl

theorem lanes_shl7 (n : ℕ) : Nat.shiftLeft (lanes n fun _ => 1) 7 = lanes n (fun _ => 128) := by
  have e : Nat.shiftLeft (lanes n fun _ => 1) 7 = lanes n (fun _ => 1) * 2 ^ 7 :=
    Nat.shiftLeft_eq _ _
  rw [e, lanes_mul]
  exact lanes_congr fun t _ => by norm_num

theorem laneH_eq : Nat.shiftLeft CFSG.KC.Misc.G24.laneOnes 7 = lanes 144 (fun _ => 128) := by
  rw [laneOnes_eq]
  exact lanes_shl7 144

theorem csub_cs {n : ℕ} {f : ℕ → ℕ} {c : ℕ} (hf : ∀ t < n, f t < 128) (hc : c ≤ 128) :
    CFSG.KC.Ord.csub 8 (lanes n fun _ => 1) (lanes n fun _ => 128) c (lanes n f) =
      lanes n (fun t => cs c (f t)) :=
  csub_lanes hf hc

theorem red3_lanes {f : ℕ → ℕ} (hf : ∀ t < 144, f t < 96) :
    CFSG.KC.Misc.G24.red3 (lanes 144 f) = lanes 144 (fun t => f t % 3) := by
  unfold CFSG.KC.Misc.G24.red3
  simp only [CFSG.KS.PK.letN_eq]
  rw [laneH_eq, laneOnes_eq]
  have b1 : ∀ t < 144, f t < 128 := fun t ht => by have := hf t ht; omega
  have b2 : ∀ t < 144, cs 48 (f t) < 128 := fun t ht => by
    have := cs_le 48 (f t); have := hf t ht; omega
  have b3 : ∀ t < 144, cs 24 (cs 48 (f t)) < 128 := fun t ht => by
    have := cs_le 24 (cs 48 (f t)); have := cs_le 48 (f t); have := hf t ht; omega
  have b4 : ∀ t < 144, cs 12 (cs 24 (cs 48 (f t))) < 128 := fun t ht => by
    have := cs_le 12 (cs 24 (cs 48 (f t))); have := cs_le 24 (cs 48 (f t))
    have := cs_le 48 (f t); have := hf t ht; omega
  have b5 : ∀ t < 144, cs 6 (cs 12 (cs 24 (cs 48 (f t)))) < 128 := fun t ht => by
    have := cs_le 6 (cs 12 (cs 24 (cs 48 (f t)))); have := cs_le 12 (cs 24 (cs 48 (f t)))
    have := cs_le 24 (cs 48 (f t)); have := cs_le 48 (f t); have := hf t ht; omega
  rw [csub_cs b1 (by norm_num), csub_cs b2 (by norm_num), csub_cs b3 (by norm_num),
    csub_cs b4 (by norm_num), csub_cs b5 (by norm_num)]
  exact lanes_congr fun t ht => r3_eq _ (hf t ht)

theorem lanes_rows (d : ℕ) (f : ℕ → ℕ) : ∀ m, lanes (d * m) f =
    ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range d, f (d * i + j) * 2 ^ (8 * (d * i + j))
  | 0 => by simp [lanes]
  | m + 1 => by
    rw [Finset.sum_range_succ, ← lanes_rows d f m, Nat.mul_succ]
    unfold lanes
    rw [Finset.sum_range_add]

theorem div_mod_idx {d i j : ℕ} (hj : j < d) : (d * i + j) / d = i ∧ (d * i + j) % d = j := by
  have hd : 0 < d := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hj, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]

theorem colMask_eq : CFSG.KC.Misc.G24.colMask =
    lanes 144 (fun t => if t % 12 = 0 then 255 else 0) := by
  have h1 : lanes (12 * 12) (fun t => if t % 12 = 0 then 255 else 0) = 255 * repu 96 12 := by
    rw [lanes_rows, repu, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single 0]
    · have e : 8 * (12 * i + 0) = 96 * i := by ring
      rw [e]
      simp
    · intro j hj hj0
      rw [(div_mod_idx (i := i) (Finset.mem_range.1 hj)).2]
      simp [hj0]
    · intro h0
      exact absurd (Finset.mem_range.2 (by norm_num)) h0
  have h2 : lanes 144 (fun t => if t % 12 = 0 then 255 else 0) =
      lanes (12 * 12) (fun t => if t % 12 = 0 then 255 else 0) := rfl
  rw [h2, h1, repu_eq (s := 96) (m := 12) (by norm_num)]
  unfold CFSG.KC.Misc.G24.colMask
  rw [shl1_eq, shl1_eq]
  have h3 : (2 : ℕ) ^ (96 * 12) = 2 ^ 1152 := by rw [show 96 * 12 = 1152 from rfl]
  rw [h3]
  generalize (2 : ℕ) ^ 1152 = N
  rfl

theorem col_eq {a : ℕ → ℕ} (ha : ∀ t < 144, a t < 256) {k : ℕ} (hk : k < 12) :
    (lanes 144 a >>> (8 * k)) &&& CFSG.KC.Misc.G24.colMask =
      ∑ i ∈ Finset.range 12, a (12 * i + k) * 2 ^ (96 * i) := by
  rw [colMask_eq, lanes_shr ha k]
  have hs : ∀ t < 144, (if t + k < 144 then a (t + k) else 0) < 256 := by
    intro t _
    split
    · exact ha _ (by assumption)
    · omega
  have hm : ∀ t < 144, (if t % 12 = 0 then 255 else 0) < 256 := fun t _ => by
    split <;> omega
  rw [lanes_and hs hm]
  have e : lanes 144 (fun t => (if t + k < 144 then a (t + k) else 0) &&&
      (if t % 12 = 0 then 255 else 0)) =
      lanes (12 * 12) (fun t => if t % 12 = 0 then a (t + k) else 0) := by
    refine lanes_congr fun t ht => ?_
    by_cases h0 : t % 12 = 0
    · have h1 : t + k < 144 := by omega
      simp only [h0, h1, ↓reduceIte]
      rw [show (255 : ℕ) = 2 ^ 8 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt (by simpa using ha _ h1)]
    · simp [h0]
  rw [e, lanes_rows]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single 0]
  · have e2 : (12 * i + 0) % 12 = 0 := by omega
    have e3 : 8 * (12 * i + 0) = 96 * i := by ring
    rw [e2, e3, if_pos rfl, Nat.add_zero]
  · intro j hj hj0
    rw [(div_mod_idx (i := i) (Finset.mem_range.1 hj)).2]
    simp [hj0]
  · intro h0
    exact absurd (Finset.mem_range.2 (by norm_num)) h0

theorem row_eq {g : ℕ → ℕ} (hg : ∀ t < 144, g t < 256) {k : ℕ} (hk : k < 12) :
    (lanes 144 g >>> (96 * k)) &&& (2 ^ 96 - 1) = lanes 12 (fun j => g (12 * k + j)) := by
  have hg' : ∀ t < 12, g (12 * k + t) < 256 := fun t ht => hg _ (by omega)
  refine lanes_ext hg' fun t r hr => ?_
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  have e : 96 * k + (8 * t + r) = 8 * (12 * k + t) + r := by ring
  rw [e, testBit_lanes hg (12 * k + t) r hr]
  by_cases ht : t < 12
  · have h1 : 12 * k + t < 144 := by omega
    have h2 : 8 * t + r < 96 := by omega
    simp [ht, h1, h2]
  · have h2 : ¬ 8 * t + r < 96 := by omega
    simp [ht, h2]

@[expose] def prodL (a b : ℕ → ℕ) (t : ℕ) : ℕ :=
  ∑ k ∈ Finset.range 12, a (12 * (t / 12) + k) * b (12 * k + t % 12)

theorem mulF3_rec (A B : ℕ) : ∀ m, (Nat.rec (motive := fun _ => ℕ) 0
    (fun k acc => Nat.add acc (Nat.mul
      (Nat.land (Nat.shiftRight A (Nat.mul 8 k)) CFSG.KC.Misc.G24.colMask)
      (Nat.land (Nat.shiftRight B (Nat.mul 96 k)) (Nat.sub (Nat.shiftLeft 1 96) 1)))) m : ℕ) =
    ∑ k ∈ Finset.range m, ((A >>> (8 * k)) &&& CFSG.KC.Misc.G24.colMask) *
      ((B >>> (96 * k)) &&& (2 ^ 96 - 1))
  | 0 => rfl
  | m + 1 => by
    rw [Finset.sum_range_succ, ← mulF3_rec A B m]
    rfl

theorem mulSum_lanes {a b : ℕ → ℕ} (ha : ∀ t < 144, a t < 256) (hb : ∀ t < 144, b t < 256) :
    ∑ k ∈ Finset.range 12, ((lanes 144 a >>> (8 * k)) &&& CFSG.KC.Misc.G24.colMask) *
      ((lanes 144 b >>> (96 * k)) &&& (2 ^ 96 - 1)) = lanes 144 (prodL a b) := by
  calc _ = ∑ k ∈ Finset.range 12, ∑ i ∈ Finset.range 12, ∑ j ∈ Finset.range 12,
        a (12 * i + k) * b (12 * k + j) * 2 ^ (8 * (12 * i + j)) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' := Finset.mem_range.1 hk
        rw [col_eq ha hk', row_eq hb hk', Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        unfold lanes
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have e : 2 ^ (96 * i) * 2 ^ (8 * j) = 2 ^ (8 * (12 * i + j)) := by
          rw [← Nat.pow_add]
          congr 1
          ring
        calc a (12 * i + k) * 2 ^ (96 * i) * (b (12 * k + j) * 2 ^ (8 * j)) =
            a (12 * i + k) * b (12 * k + j) * (2 ^ (96 * i) * 2 ^ (8 * j)) := by ring
          _ = _ := by rw [e]
    _ = ∑ i ∈ Finset.range 12, ∑ j ∈ Finset.range 12, ∑ k ∈ Finset.range 12,
        a (12 * i + k) * b (12 * k + j) * 2 ^ (8 * (12 * i + j)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := by
        have h144 : lanes 144 (prodL a b) = lanes (12 * 12) (prodL a b) := rfl
        rw [h144, lanes_rows]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
        obtain ⟨e1, e2⟩ := div_mod_idx (d := 12) (i := i) (Finset.mem_range.1 hj)
        unfold prodL
        rw [e1, e2, Finset.sum_mul]

theorem prodL_le {a b : ℕ → ℕ} (ha : ∀ t < 144, a t < 3) (hb : ∀ t < 144, b t < 3) {t : ℕ}
    (ht : t < 144) : prodL a b t ≤ 48 := by
  unfold prodL
  calc ∑ k ∈ Finset.range 12, a (12 * (t / 12) + k) * b (12 * k + t % 12)
      ≤ ∑ _k ∈ Finset.range 12, 4 := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' := Finset.mem_range.1 hk
        have h1 := ha (12 * (t / 12) + k) (by omega)
        have h2 := hb (12 * k + t % 12) (by omega)
        calc a (12 * (t / 12) + k) * b (12 * k + t % 12) ≤ 2 * 2 :=
            Nat.mul_le_mul (by omega) (by omega)
          _ = 4 := by norm_num
    _ = 48 := by simp

theorem mulF3_lanes {a b : ℕ → ℕ} (ha : ∀ t < 144, a t < 3) (hb : ∀ t < 144, b t < 3) :
    CFSG.KC.Misc.G24.mulF3 (lanes 144 a) (lanes 144 b) =
      lanes 144 (fun t => prodL a b t % 3) := by
  have ha' : ∀ t < 144, a t < 256 := fun t ht => by have := ha t ht; omega
  have hb' : ∀ t < 144, b t < 256 := fun t ht => by have := hb t ht; omega
  unfold CFSG.KC.Misc.G24.mulF3
  simp only [CFSG.KS.PK.letN_eq]
  rw [mulF3_rec _ _ 12, mulSum_lanes ha' hb']
  exact red3_lanes fun t ht => by have := prodL_le ha hb ht; omega

@[expose] def Canon3 (X : ℕ) : Prop := X < 2 ^ (8 * 144) ∧ ∀ t < 144, lane8 X t < 3

@[expose] def pkMat3 (X : ℕ) : Matrix (Fin 12) (Fin 12) (ZMod 3) :=
  Matrix.of fun i j => ((lane8 X (12 * i.val + j.val) : ℕ) : ZMod 3)

theorem canon3_iff {X : ℕ} : Canon3 X ↔ ∃ a : ℕ → ℕ, (∀ t < 144, a t < 3) ∧ X = lanes 144 a := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨lane8 X, h2, lanes_lane8 h1⟩
  · rintro ⟨a, ha, hX⟩
    have ha' : ∀ t < 144, a t < 256 := fun t ht => by have := ha t ht; omega
    rw [hX]
    exact ⟨lanes_lt ha', fun t ht => by rw [lane8_lanes ha' ht]; exact ha t ht⟩

theorem pkMat3_lanes {a : ℕ → ℕ} (ha : ∀ t < 144, a t < 3) (i j : Fin 12) :
    pkMat3 (lanes 144 a) i j = ((a (12 * i.val + j.val) : ℕ) : ZMod 3) := by
  have ha' : ∀ t < 144, a t < 256 := fun t ht => by have := ha t ht; omega
  have hi := i.isLt
  have hj := j.isLt
  show ((lane8 (lanes 144 a) (12 * i.val + j.val) : ℕ) : ZMod 3) = _
  rw [lane8_lanes ha' (by omega)]

theorem canon3_mulF3 {A B : ℕ} (hA : Canon3 A) (hB : Canon3 B) :
    Canon3 (CFSG.KC.Misc.G24.mulF3 A B) ∧
      pkMat3 (CFSG.KC.Misc.G24.mulF3 A B) = pkMat3 A * pkMat3 B := by
  obtain ⟨a, ha, hAa⟩ := canon3_iff.1 hA
  obtain ⟨b, hb, hBb⟩ := canon3_iff.1 hB
  rw [hAa, hBb, mulF3_lanes ha hb]
  have hp : ∀ t < 144, prodL a b t % 3 < 3 := fun t _ => Nat.mod_lt _ (by norm_num)
  refine ⟨canon3_iff.2 ⟨_, hp, rfl⟩, ?_⟩
  ext i j
  rw [Matrix.mul_apply, pkMat3_lanes hp, Finset.sum_congr rfl fun k _ => by
    rw [pkMat3_lanes ha, pkMat3_lanes hb]]
  rw [ZMod.natCast_mod]
  unfold prodL
  obtain ⟨e1, e2⟩ := div_mod_idx (d := 12) (i := i.val) j.isLt
  rw [e1, e2, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range
    (fun k => ((a (12 * i.val + k) * b (12 * k + j.val) : ℕ) : ZMod 3)) 12]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.cast_mul]

theorem one3_eq : CFSG.KC.Misc.G24.one3 =
    lanes 144 (fun t => if t / 12 = t % 12 then 1 else 0) := by
  have h1 : lanes (12 * 12) (fun t => if t / 12 = t % 12 then 1 else 0) = repu 104 12 := by
    rw [lanes_rows, repu]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single i]
    · obtain ⟨e1, e2⟩ := div_mod_idx (d := 12) (i := i) (Finset.mem_range.1 hi)
      rw [e1, e2, if_pos rfl, Nat.one_mul]
      congr 1
      ring
    · intro j hj hji
      obtain ⟨e1, e2⟩ := div_mod_idx (d := 12) (i := i) (Finset.mem_range.1 hj)
      rw [e1, e2, if_neg (Ne.symm hji), Nat.zero_mul]
    · intro h0
      exact absurd hi h0
  have h2 : lanes 144 (fun t => if t / 12 = t % 12 then 1 else 0) =
      lanes (12 * 12) (fun t => if t / 12 = t % 12 then 1 else 0) := rfl
  rw [h2, h1, repu_eq (s := 104) (m := 12) (by norm_num)]
  unfold CFSG.KC.Misc.G24.one3
  rw [shl1_eq, shl1_eq]
  have h3 : (2 : ℕ) ^ (104 * 12) = 2 ^ 1248 := by rw [show 104 * 12 = 1248 from rfl]
  rw [h3]
  generalize (2 : ℕ) ^ 1248 = N
  rfl

theorem canon3_one3 : Canon3 CFSG.KC.Misc.G24.one3 ∧ pkMat3 CFSG.KC.Misc.G24.one3 = 1 := by
  rw [one3_eq]
  have hp : ∀ t < 144, (if t / 12 = t % 12 then 1 else 0) < 3 := fun t _ => by
    split <;> omega
  refine ⟨canon3_iff.2 ⟨_, hp, rfl⟩, ?_⟩
  ext i j
  rw [pkMat3_lanes hp, Matrix.one_apply]
  obtain ⟨e1, e2⟩ := div_mod_idx (d := 12) (i := i.val) j.isLt
  rw [e1, e2]
  by_cases h : i = j
  · subst h
    simp
  · have h' : ¬ i.val = j.val := fun e => h (Fin.ext e)
    simp [h, h']

theorem canon3_inj {A B : ℕ} (hA : Canon3 A) (hB : Canon3 B) (h : pkMat3 A = pkMat3 B) :
    A = B := by
  have key : ∀ t < 144, lane8 A t = lane8 B t := by
    intro t ht
    have hi : t / 12 < 12 := by omega
    have hj : t % 12 < 12 := Nat.mod_lt _ (by norm_num)
    have h1 := congrFun (congrFun h ⟨t / 12, hi⟩) ⟨t % 12, hj⟩
    simp only [pkMat3, Matrix.of_apply] at h1
    have e : 12 * (t / 12) + t % 12 = t := by omega
    rw [e] at h1
    have h2 := (ZMod.natCast_eq_natCast_iff' _ _ 3).1 h1
    rw [Nat.mod_eq_of_lt (hA.2 t ht), Nat.mod_eq_of_lt (hB.2 t ht)] at h2
    exact h2
  rw [lanes_lane8 (n := 144) hA.1, lanes_lane8 (n := 144) hB.1]
  exact lanes_congr key

@[expose] noncomputable def rowPack (i : ℕ) (r : List ℕ) (acc : ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => acc)
    (fun d _ ih2 j => Nat.lor (Nat.shiftLeft d (Nat.mul 8 (Nat.add (Nat.mul 12 i) j)))
      (ih2 (Nat.succ j))) r

theorem packRows3_cons (r : List ℕ) (rs : List (List ℕ)) (i acc : ℕ) :
    CFSG.KC.Misc.G24.packRows3 (r :: rs) i acc =
      CFSG.KC.Misc.G24.packRows3 rs (i + 1) (rowPack i r acc 0) := rfl

theorem packRows3_nil (i acc : ℕ) : CFSG.KC.Misc.G24.packRows3 [] i acc = acc := rfl

theorem rowPack_nil (i acc j : ℕ) : rowPack i [] acc j = acc := rfl

theorem rowPack_cons (i d : ℕ) (r : List ℕ) (acc j : ℕ) :
    rowPack i (d :: r) acc j = (d <<< (8 * (12 * i + j))) ||| rowPack i r acc (j + 1) := rfl

theorem testBit_rowPack (i : ℕ) (r : List ℕ) (acc q : ℕ) : ∀ j,
    (rowPack i r acc j).testBit q = true ↔
      acc.testBit q = true ∨ ∃ t < r.length,
        ((r.getD t 0) <<< (8 * (12 * i + (j + t)))).testBit q = true := by
  induction r with
  | nil => intro j; simp [rowPack_nil]
  | cons d r ih =>
    intro j
    rw [rowPack_cons, Nat.testBit_or, Bool.or_eq_true, ih (j + 1)]
    constructor
    · rintro (h | h | ⟨t, ht, h⟩)
      · exact Or.inr ⟨0, by simp, by simpa using h⟩
      · exact Or.inl h
      · refine Or.inr ⟨t + 1, by simpa using ht, ?_⟩
        rw [show j + (t + 1) = j + 1 + t by omega]
        simpa using h
    · rintro (h | ⟨t, ht, h⟩)
      · exact Or.inr (Or.inl h)
      · cases t with
        | zero => exact Or.inl (by simpa using h)
        | succ t =>
          refine Or.inr (Or.inr ⟨t, by simpa using ht, ?_⟩)
          rw [show j + 1 + t = j + (t + 1) by omega]
          simpa using h

theorem testBit_packRows3 (rs : List (List ℕ)) (q : ℕ) : ∀ (acc i : ℕ),
    (CFSG.KC.Misc.G24.packRows3 rs i acc).testBit q = true ↔
      acc.testBit q = true ∨ ∃ s < rs.length, ∃ t < (rs.getD s []).length,
        (((rs.getD s []).getD t 0) <<< (8 * (12 * (i + s) + t))).testBit q = true := by
  induction rs with
  | nil => intro acc i; simp [packRows3_nil]
  | cons r rs ih =>
    intro acc i
    rw [packRows3_cons, ih, testBit_rowPack]
    constructor
    · rintro ((h | ⟨t, ht, h⟩) | ⟨s, hs, t, ht, h⟩)
      · exact Or.inl h
      · refine Or.inr ⟨0, by simp, t, by simpa using ht, ?_⟩
        simpa using h
      · refine Or.inr ⟨s + 1, by simpa using hs, t, by simpa using ht, ?_⟩
        rw [show i + (s + 1) = i + 1 + s by omega]
        simpa using h
    · rintro (h | ⟨s, hs, t, ht, h⟩)
      · exact Or.inl (Or.inl h)
      · cases s with
        | zero => exact Or.inl (Or.inr ⟨t, by simpa using ht, by simpa using h⟩)
        | succ s =>
          refine Or.inr ⟨s, by simpa using hs, t, by simpa using ht, ?_⟩
          rw [show i + 1 + s = i + (s + 1) by omega]
          simpa using h

theorem shape12_iff (rs : List (List ℕ)) : CFSG.KC.Misc.G24.shape12 rs = true ↔
    rs.length = 12 ∧ ∀ r ∈ rs, r.length = 12 := by
  unfold CFSG.KC.Misc.G24.shape12
  rw [CFSG.KS.PK.andB_eq, Bool.and_eq_true, Nat.beq_eq, CFSG.KS.PK.allLL_iff, lenLLK_eq]
  refine and_congr Iff.rfl (forall_congr' fun r => forall_congr' fun _ => ?_)
  rw [Nat.beq_eq, CFSG.KS.PK.lenN_misc_eq]

theorem packRows3_lanes {rs : List (List ℕ)} (hs : CFSG.KC.Misc.G24.shape12 rs = true)
    (hd : ∀ r ∈ rs, ∀ d ∈ r, d < 256) :
    CFSG.KC.Misc.G24.packRows3 rs 0 0 =
      lanes 144 (fun u => (rs.getD (u / 12) []).getD (u % 12) 0) := by
  obtain ⟨hlen, hrow⟩ := (shape12_iff rs).1 hs
  have hmem : ∀ s < 12, rs.getD s [] ∈ rs := by
    intro s hs'
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    simp
  have hentry : ∀ s < 12, ∀ t < 12, (rs.getD s []).getD t 0 < 256 := by
    intro s hs' t ht
    have h1 := hrow _ (hmem s hs')
    exact hd _ (hmem s hs') _ (getD_mem_of_lt (by omega))
  have hg : ∀ u < 144, (fun u => (rs.getD (u / 12) []).getD (u % 12) 0) u < 256 := fun u hu =>
    hentry (u / 12) (by omega) (u % 12) (Nat.mod_lt _ (by norm_num))
  refine lanes_ext hg fun u b hb => ?_
  rw [Bool.eq_iff_iff, testBit_packRows3]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, Nat.zero_add, Nat.testBit_shiftLeft,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨s, hs', t, ht, h1, h2⟩
    rw [hlen] at hs'
    rw [hrow _ (hmem s hs')] at ht
    have hx := hentry s hs' t ht
    have hk : 8 * u + b - 8 * (12 * s + t) < 8 := by
      by_contra hcon
      have := Nat.testBit_lt_two_pow (x := (rs.getD s []).getD t 0)
        (i := 8 * u + b - 8 * (12 * s + t))
        (Nat.lt_of_lt_of_le hx (by
          calc 256 = 2 ^ 8 := by norm_num
            _ ≤ 2 ^ (8 * u + b - 8 * (12 * s + t)) :=
              Nat.pow_le_pow_right (by norm_num) (by omega)))
      rw [this] at h2
      exact absurd h2 (by simp)
    have hu' : u = 12 * s + t := by omega
    refine ⟨by omega, ?_⟩
    have e1 : u / 12 = s := by omega
    have e2 : u % 12 = t := by omega
    rw [e1, e2]
    have e3 : 8 * u + b - 8 * (12 * s + t) = b := by omega
    rwa [e3] at h2
  · rintro ⟨hu, h⟩
    refine ⟨u / 12, by rw [hlen]; omega, u % 12, ?_, ?_, ?_⟩
    · rw [hrow _ (hmem _ (by omega))]
      exact Nat.mod_lt _ (by norm_num)
    · omega
    · have e3 : 8 * u + b - 8 * (12 * (u / 12) + u % 12) = b := by omega
      rw [e3]
      exact h

@[expose] def digMat3 (ds : List (List ℕ)) : Matrix (Fin 12) (Fin 12) (ZMod 3) :=
  Matrix.of fun i j => (((ds.getD i.val []).getD j.val 0 : ℕ) : ZMod 3)

theorem canon3_pack {rs : List (List ℕ)} (hs : CFSG.KC.Misc.G24.shape12 rs = true)
    (hd : ∀ r ∈ rs, ∀ d ∈ r, d < 3) :
    Canon3 (CFSG.KC.Misc.G24.packRows3 rs 0 0) ∧
      pkMat3 (CFSG.KC.Misc.G24.packRows3 rs 0 0) = digMat3 rs := by
  have hd' : ∀ r ∈ rs, ∀ d ∈ r, d < 256 := fun r hr d hdr => by
    have := hd r hr d hdr
    omega
  rw [packRows3_lanes hs hd']
  obtain ⟨hlen, hrow⟩ := (shape12_iff rs).1 hs
  have hmem : ∀ s < 12, rs.getD s [] ∈ rs := by
    intro s hs'
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    simp
  have ha : ∀ u < 144, (fun u => (rs.getD (u / 12) []).getD (u % 12) 0) u < 3 := by
    intro u hu
    exact hd _ (hmem _ (by omega)) _ (getD_mem_of_lt (by rw [hrow _ (hmem _ (by omega))]; omega))
  refine ⟨canon3_iff.2 ⟨_, ha, rfl⟩, ?_⟩
  ext i j
  rw [pkMat3_lanes ha]
  obtain ⟨e1, e2⟩ := div_mod_idx (d := 12) (i := i.val) j.isLt
  simp only [digMat3, Matrix.of_apply, e1, e2]

theorem word3_eval {Lb Lib : List ℕ} {M N : ℕ → Matrix (Fin 12) (Fin 12) (ZMod 3)}
    (hb : ∀ i < 6, Canon3 (Lb.getD i 0) ∧ pkMat3 (Lb.getD i 0) = M i)
    (hi : ∀ i < 6, Canon3 (Lib.getD i 0) ∧ pkMat3 (Lib.getD i 0) = N i)
    (w : List (Fin 6 × Bool)) :
    Canon3 (CFSG.KC.Misc.G24.word3 Lb Lib (encG w)) ∧
      pkMat3 (CFSG.KC.Misc.G24.word3 Lb Lib (encG w)) =
        wordProd (fun l : Fin 6 × Bool => if l.2 then M l.1.val else N l.1.val) w := by
  induction w with
  | nil =>
    exact canon3_one3
  | cons l w ih =>
    have hl : encL l / 2 = l.1.val := by
      unfold encL
      split <;> omega
    have e : CFSG.KC.Misc.G24.word3 Lb Lib (encG (l :: w)) =
        CFSG.KC.Misc.G24.mulF3 (if l.2 then Lb.getD l.1.val 0 else Lib.getD l.1.val 0)
          (CFSG.KC.Misc.G24.word3 Lb Lib (encG w)) := by
      show CFSG.KC.Misc.G24.mulF3 (Bool.rec (motive := fun _ => ℕ)
        (CFSG.KC.Misc.G24.nthV Lib (Nat.div (encL l) 2))
        (CFSG.KC.Misc.G24.nthV Lb (Nat.div (encL l) 2))
        (Nat.beq (Nat.mod (encL l) 2) 1)) (CFSG.KC.Misc.G24.word3 Lb Lib (encG w)) = _
      have hd : Nat.div (encL l) 2 = l.1.val := hl
      rw [hd]
      obtain ⟨⟨i, hi'⟩, bb⟩ := l
      cases bb
      · have : Nat.beq (Nat.mod (encL (⟨i, hi'⟩, false)) 2) 1 = false := by
          unfold encL
          simp only [Bool.false_eq_true, if_false, Nat.add_zero]
          show Nat.beq ((2 * i) % 2) 1 = false
          rw [Nat.mul_mod_right]
          rfl
        rw [this]
        show CFSG.KC.Misc.G24.mulF3 (CFSG.KC.Misc.G24.nthV Lib i) _ = _
        rw [nthV_eq]
        simp
      · have : Nat.beq (Nat.mod (encL (⟨i, hi'⟩, true)) 2) 1 = true := by
          unfold encL
          simp only [if_true]
          show Nat.beq ((2 * i + 1) % 2) 1 = true
          rw [Nat.mul_add_mod]
          rfl
        rw [this]
        show CFSG.KC.Misc.G24.mulF3 (CFSG.KC.Misc.G24.nthV Lb i) _ = _
        rw [nthV_eq]
        simp
    rw [e]
    obtain ⟨hc1, hc2⟩ := ih
    have hm : Canon3 (if l.2 then Lb.getD l.1.val 0 else Lib.getD l.1.val 0) ∧
        pkMat3 (if l.2 then Lb.getD l.1.val 0 else Lib.getD l.1.val 0) =
          (if l.2 then M l.1.val else N l.1.val) := by
      split
      · exact hb _ l.1.isLt
      · exact hi _ l.1.isLt
    obtain ⟨hp1, hp2⟩ := canon3_mulF3 hm.1 hc1
    exact ⟨hp1, by rw [hp2, hm.2, hc2]; rfl⟩

end CFSG.KC.Misc.Spec

end
