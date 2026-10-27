module

public import Certificates.Data.Kernel.KDense.KeysDistinct
public import CFSG.Certificates.Kernel.KDense.SortSound
public import CFSG.Certificates.Kernel.KDense.SepSpread
public import CFSG.Certificates.Kernel.Trace6091.TwinEq
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.KDense

open CFSG.Monster.AxisCount

@[expose] noncomputable def keyRecAt (KT p : Nat) : Nat := KT / 2 ^ (32 * p) % 2 ^ 32

namespace KeysOKAux

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.Benes
open CFSG.Monster.B CFSG.KC.Trace6091 CFSG.KC.KDense.TabAux

@[expose] def D (B n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ i ∈ Finset.range n, B ^ i * f i

theorem D_succ (B n : ℕ) (f : ℕ → ℕ) : D B (n + 1) f = D B n f + B ^ n * f n :=
  Finset.sum_range_succ _ _

theorem D_succ' (B : ℕ) (f : ℕ → ℕ) : ∀ n, D B (n + 1) f = f 0 + B * D B n (fun i => f (i + 1))
  | 0 => by simp [D]
  | n + 1 => by
    rw [D_succ, D_succ' B f n, D_succ, pow_succ']
    ring

theorem D_lt {B n : ℕ} {f : ℕ → ℕ} (hf : ∀ i < n, f i < B) : D B n f < B ^ n := by
  induction n with
  | zero => simp [D]
  | succ n ih =>
    rw [D_succ, pow_succ]
    have h1 := ih (fun i hi => hf i (by omega))
    have h2 : f n + 1 ≤ B := hf n (by omega)
    calc D B n f + B ^ n * f n < B ^ n + B ^ n * f n := by omega
      _ = B ^ n * (f n + 1) := by ring
      _ ≤ B ^ n * B := Nat.mul_le_mul_left _ h2

theorem D_digit {B n : ℕ} {f : ℕ → ℕ} (hB : 0 < B) (hf : ∀ i < n, f i < B) {j : ℕ}
    (hj : j < n) : D B n f / B ^ j % B = f j := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [D_succ]
    have hD := D_lt (fun i hi => hf i (by omega) : ∀ i < n, f i < B)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
    · have e : B ^ n * f n = B ^ j * (B * (B ^ (n - j - 1) * f n)) := by
        have en : B ^ n = B ^ j * B * B ^ (n - j - 1) := by
          rw [← pow_succ, ← pow_add]
          congr 1
          omega
        rw [en]
        ring
      rw [e, Nat.add_mul_div_left _ _ (pow_pos hB _), Nat.add_mul_mod_self_left]
      exact ih (fun i hi => hf i (by omega)) h
    · rw [Nat.add_mul_div_left _ _ (pow_pos hB _), Nat.div_eq_of_lt hD, Nat.zero_add,
        Nat.mod_eq_of_lt (hf j hj)]

theorem D_recon (B x : ℕ) : ∀ n, D B n (fun i => x / B ^ i % B) = x % B ^ n
  | 0 => by simp [D, Nat.mod_one]
  | n + 1 => by rw [D_succ, D_recon B x n, Nat.mod_pow_succ]

theorem D_add (B n : ℕ) (f g : ℕ → ℕ) : D B n f + D B n g = D B n (fun i => f i + g i) := by
  simp only [D, Nat.mul_add, Finset.sum_add_distrib]

theorem D_congr {B n : ℕ} {f g : ℕ → ℕ} (h : ∀ i < n, f i = g i) : D B n f = D B n g :=
  Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]

theorem testBit_D {B s n : ℕ} {g : ℕ → ℕ} (hB : B = 2 ^ s) (hs : 0 < s) (hg : ∀ i < n, g i < B)
    (k : ℕ) : (D B n g).testBit k = (decide (k / s < n) && (g (k / s)).testBit (k % s)) := by
  subst hB
  by_cases hq : k / s < n
  · rw [decide_eq_true hq, Bool.true_and]
    have e : k = k % s + s * (k / s) := by rw [Nat.add_comm, Nat.div_add_mod]
    have h1 : D (2 ^ s) n g / 2 ^ (s * (k / s)) % 2 ^ s = g (k / s) := by
      rw [pow_mul]
      exact D_digit (Nat.two_pow_pos s) hg hq
    conv_lhs => rw [e]
    rw [← Nat.testBit_div_two_pow, ← h1, Nat.testBit_mod_two_pow, decide_eq_true (Nat.mod_lt _ hs),
      Bool.true_and]
  · rw [decide_eq_false hq, Bool.false_and]
    apply Nat.testBit_lt_two_pow
    calc D (2 ^ s) n g < (2 ^ s) ^ n := D_lt hg
      _ = 2 ^ (s * n) := (pow_mul 2 s n).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by
          have := Nat.div_mul_le_self k s
          have : n * s ≤ k / s * s := Nat.mul_le_mul_right _ (by omega)
          rw [Nat.mul_comm s n]
          omega)

theorem land_D {B s w n : ℕ} (hB : B = 2 ^ s) (hs : 0 < s) (hw : w ≤ s) (v : ℕ) :
    v &&& D B n (fun _ => 2 ^ w - 1) = D B n (fun i => v / 2 ^ (s * i) % 2 ^ w) := by
  have hw' : 2 ^ w ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) hw
  have hw0 : 0 < 2 ^ w := Nat.two_pow_pos w
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, testBit_D hB hs (fun i _ => by omega) k,
    testBit_D hB hs (fun i _ => lt_of_lt_of_le (Nat.mod_lt _ hw0) (hB ▸ hw')) k,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  have e : k % s + s * (k / s) = k := by rw [Nat.add_comm, Nat.div_add_mod]
  rw [e]
  cases v.testBit k <;> cases decide (k / s < n) <;> simp

theorem st1 {v : ℕ} (hv : v < 2 ^ 24) :
    v - ((v >>> 1) &&& 5592405) = D 4 12 (fun i => v / 4 ^ i % 2 + v / 4 ^ i / 2 % 2) := by
  have hM : (5592405 : ℕ) = D 4 12 (fun _ => 2 ^ 1 - 1) := by
    simp only [D, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  rw [hM, land_D (s := 2) (by norm_num) (by norm_num) (by norm_num)]
  have hr : D 4 12 (fun i => v / 4 ^ i % 4) = v := by
    rw [D_recon, Nat.mod_eq_of_lt]
    simpa using hv
  have hs : D 4 12 (fun i => v / 4 ^ i % 2 + v / 4 ^ i / 2 % 2) +
      D 4 12 (fun i => v >>> 1 / 2 ^ (2 * i) % 2 ^ 1) = v := by
    rw [D_add]
    conv_rhs => rw [← hr]
    refine D_congr fun i _ => ?_
    have e : v >>> 1 / 2 ^ (2 * i) = v / 4 ^ i / 2 := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, pow_mul]
      norm_num
      ring_nf
    rw [e]
    omega
  omega

theorem st2 {c : ℕ → ℕ} (hc : ∀ i < 12, c i < 4) :
    (D 4 12 c &&& 3355443) + ((D 4 12 c >>> 2) &&& 3355443) =
      D 16 6 (fun j => c (2 * j) + c (2 * j + 1)) := by
  have hM : (3355443 : ℕ) = D 16 6 (fun _ => 2 ^ 2 - 1) := by
    simp only [D, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  rw [hM, land_D (s := 4) (by norm_num) (by norm_num) (by norm_num),
    land_D (s := 4) (by norm_num) (by norm_num) (by norm_num), D_add]
  refine D_congr fun j hj => ?_
  have e1 : (2 : ℕ) ^ (4 * j) = 4 ^ (2 * j) := by
    rw [pow_mul, pow_mul]
    norm_num
  have e2 : D 4 12 c >>> 2 / 2 ^ (4 * j) = D 4 12 c / 4 ^ (2 * j + 1) := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, e1, pow_succ]
    norm_num
    ring_nf
  rw [e2, e1]
  norm_num
  rw [D_digit (by norm_num) hc (by omega), D_digit (by norm_num) hc (by omega)]

theorem st3 {e : ℕ → ℕ} (he : ∀ i ≤ 6, e i < 8) (h6 : e 6 = 0) :
    (D 16 6 e + (D 16 6 e >>> 4)) &&& 986895 = D 256 3 (fun k => e (2 * k) + e (2 * k + 1)) := by
  have hM : (986895 : ℕ) = D 256 3 (fun _ => 2 ^ 4 - 1) := by
    simp only [D, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have hsh : D 16 6 e >>> 4 = D 16 6 (fun i => e (i + 1)) := by
    rw [Nat.shiftRight_eq_div_pow, D_succ', D_succ 16 5 (fun i => e (i + 1)), h6, Nat.mul_zero,
      Nat.add_zero]
    norm_num
    have := he 0 (by omega)
    omega
  rw [hsh, D_add, hM, land_D (s := 8) (by norm_num) (by norm_num) (by norm_num)]
  refine D_congr fun k hk => ?_
  have e1 : (2 : ℕ) ^ (8 * k) = 16 ^ (2 * k) := by
    rw [pow_mul, pow_mul]
    norm_num
  rw [e1]
  norm_num
  rw [D_digit (f := fun i => e i + e (i + 1)) (by norm_num)
    (fun i hi => by have := he i (by omega); have := he (i + 1) (by omega); omega) (by omega)]

theorem st4 {g : ℕ → ℕ} (hg : ∀ k < 3, g k < 256) :
    (D 256 3 g &&& 255) + ((D 256 3 g >>> 8) &&& 255) + (D 256 3 g >>> 16) = g 0 + g 1 + g 2 := by
  have h255 : (255 : ℕ) = 2 ^ 8 - 1 := rfl
  have h0 := hg 0 (by omega)
  have h1 := hg 1 (by omega)
  have h2 := hg 2 (by omega)
  rw [h255, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  simp only [D, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  omega

theorem popc24_def (a : ℕ) : popc24 a =
    (fun z => (z &&& 255) + ((z >>> 8) &&& 255) + (z >>> 16))
      ((fun y => (y + (y >>> 4)) &&& 986895)
        ((fun x => (x &&& 3355443) + ((x >>> 2) &&& 3355443))
          ((fun v => v - ((v >>> 1) &&& 5592405)) (a &&& 16777215)))) := rfl

theorem popc24_eq (a : ℕ) : popc24 a = Rep4371.Native.popcN 24 a := by
  have hv : a &&& 16777215 = a % 2 ^ 24 := Nat.and_two_pow_sub_one_eq_mod a 24
  have hlt : a % 2 ^ 24 < 2 ^ 24 := Nat.mod_lt _ (Nat.two_pow_pos 24)
  rw [popc24_def]
  dsimp only
  rw [hv, st1 hlt, st2 (fun i _ => by omega)]
  generalize hvv : a % 2 ^ 24 = v at hlt
  have hc : ∀ i, v / 4 ^ i % 2 + v / 4 ^ i / 2 % 2 ≤ 2 := fun i => by omega
  have hz : ∀ i, 12 ≤ i → v / 4 ^ i = 0 := fun i hi => Nat.div_eq_of_lt (by
    calc v < 2 ^ 24 := hlt
      _ = 4 ^ 12 := by norm_num
      _ ≤ 4 ^ i := Nat.pow_le_pow_right (by decide) hi)
  rw [st3 (fun i _ => by have := hc (2 * i); have := hc (2 * i + 1); omega)
    (by rw [hz 12 (by omega), hz 13 (by omega)]),
    st4 (fun k _ => by
      have := hc (2 * (2 * k)); have := hc (2 * (2 * k) + 1); have := hc (2 * (2 * k + 1))
      have := hc (2 * (2 * k + 1) + 1); omega)]
  rw [popcN_sum]
  have hb : ∀ i ∈ Finset.range 24, (a.testBit i).toNat = v / 2 ^ i % 2 := fun i hi => by
    rw [← hvv, ← Nat.toNat_testBit, Nat.testBit_mod_two_pow,
      decide_eq_true (Finset.mem_range.1 hi), Bool.true_and]
  rw [Finset.sum_congr rfl hb]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.div_div_eq_div_mul]
  norm_num
  omega

theorem blt_dec (a b : ℕ) : Nat.blt a b = decide (a < b) :=
  Bool.eq_iff_iff.2 (by simp [Nat.blt_eq])

theorem brec_dec (P : Prop) [Decidable P] (x y : ℕ) :
    (Bool.rec (motive := fun _ => ℕ) x y (decide P) : ℕ) = if P then y else x := by
  by_cases h : P <;> simp [h]

theorem andB_dec (P Q : Prop) [Decidable P] [Decidable Q] :
    andB (decide P) (decide Q) = decide (P ∧ Q) := by
  by_cases h : P <;> by_cases h' : Q <;> simp [andB, h, h']

theorem land_mod (x n : ℕ) : Nat.land x (2 ^ n - 1) = x % 2 ^ n := Nat.and_two_pow_sub_one_eq_mod x n

theorem keyAtPos_lo (TH OCT DU1 : ℕ) {p : ℕ} (hp : p < 65536) : keyAtPos TH OCT DU1 p =
    if p % 32 < 24 then keyRec (oddCodeT (2 * (p / 32)) (p % 32))
      (f12 TH (oddCodeT (2 * (p / 32)) (p % 32)) ^^^ f12 DU1 (p % 32)) else 0 := by
  unfold keyAtPos
  have e1 : Nat.blt p (nat_lit 65536) = true := by simpa using hp
  rw [e1]
  dsimp only
  rw [blt_dec, brec_dec]
  have l : Nat.land p (nat_lit 31) = p % 32 := land_mod p 5
  have s : Nat.shiftLeft (Nat.shiftRight p (nat_lit 5)) (nat_lit 1) = 2 * (p / 32) := by
    rw [nshl, nshr, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    norm_num
    omega
  rw [l, s]
  rfl

theorem sh_div (x n : ℕ) : Nat.shiftRight x n = x / 2 ^ n := Nat.shiftRight_eq_div_pow x n

theorem shl_one (x : ℕ) : Nat.shiftLeft (nat_lit 1) x = 2 ^ x := by
  rw [nshl, Nat.shiftLeft_eq, Nat.one_mul]

theorem shl1 (x : ℕ) : Nat.shiftLeft x (nat_lit 1) = 2 * x := by
  rw [nshl, Nat.shiftLeft_eq]
  norm_num
  ring

theorem keyAtPos_mid (TH OCT DU1 : ℕ) {p : ℕ} (hp1 : 65536 ≤ p) (hp2 : p < 114112) :
    keyAtPos TH OCT DU1 p =
      keyRec (octCodeT (f12 OCT ((p - 65536) / 64)) (2 * ((p - 65536) % 64) + parT 6 ((p - 65536) % 64)))
        (f12 TH (octCodeT (f12 OCT ((p - 65536) / 64))
            (2 * ((p - 65536) % 64) + parT 6 ((p - 65536) % 64))) ^^^
          dualL DU1 (spreadT (wordT (f12 OCT ((p - 65536) / 64)))
            (2 * ((p - 65536) % 64) + parT 6 ((p - 65536) % 64)))) := by
  unfold keyAtPos
  have e1 : Nat.blt p (nat_lit 65536) = false := by
    rw [blt_dec]
    exact decide_eq_false (Nat.not_lt.2 hp1)
  have e2 : Nat.blt p (nat_lit 114112) = true := by simpa using hp2
  rw [e1, e2]
  dsimp only
  have l : ∀ x, Nat.land x (nat_lit 63) = x % 64 := fun x => land_mod x 6
  have s : ∀ x, Nat.shiftRight x (nat_lit 6) = x / 64 := fun x => sh_div x 6
  simp only [nsub, l, s, shl1, nadd]
  rfl

theorem land31 (x : ℕ) : Nat.land x (nat_lit 31) = x % 32 := land_mod x 5

theorem shr5 (x : ℕ) : Nat.shiftRight x (nat_lit 5) = x / 32 := sh_div x 5

theorem bit10 (x : ℕ) : bitN x (nat_lit 10) = x / 1024 % 2 := by
  rw [bitN_eq, Nat.toNat_testBit]

theorem keyAtPos_hi (TH OCT DU1 : ℕ) {p pp : ℕ} (hp : 114112 ≤ p) (hpp : p - 114688 = pp) :
    keyAtPos TH OCT DU1 p =
      if pp < 2048 ∧ pp / 32 % 32 < pp % 32 ∧ pp % 32 < 24
      then keyRec (pp / 1024 % 2 * 63) (dualT (2 ^ (pp / 32 % 32) ||| 2 ^ (pp % 32))) else 0 := by
  have e1 : Nat.blt p (nat_lit 65536) = false := by
    rw [blt_dec]
    have h' : 65536 ≤ p := by omega
    exact decide_eq_false (Nat.not_lt.2 h')
  have e2 : Nat.blt p (nat_lit 114112) = false := by
    rw [blt_dec]
    exact decide_eq_false (Nat.not_lt.2 hp)
  have hq : Nat.sub p (nat_lit 114688) = pp := hpp
  unfold keyAtPos
  rw [hq, e1, e2]
  dsimp only
  simp only [land31, shr5, shl_one, bit10, blt_dec, andB_dec, brec_dec]
  rfl

theorem wordN_eq (a : ℕ) : Rep4371.Native.wordN a = Model.wordN a := rfl

theorem dualN_eq (v : ℕ) : Rep4371.Native.dualN v = Model.dualN v := rfl

theorem bmaskN_eq : Rep4371.Native.bmaskN = Model.bmaskN := rfl

theorem combN_eq (m : ℕ → ℕ) (a : ℕ) : ∀ n, Rep4371.Native.combN m n a = Model.combN m n a
  | 0 => rfl
  | n + 1 => by simp only [Rep4371.Native.combN, Model.combN, combN_eq m a n]

theorem popcN_eq : ∀ k a, Rep4371.Native.popcN k a = Model.popcN k a
  | 0, _ => rfl
  | k + 1, a => by simp only [Rep4371.Native.popcN, Model.popcN, popcN_eq k (a / 2)]

theorem packN_eq (f : ℕ → Bool) : ∀ n, Rep4371.Native.packN f n = Model.packN f n
  | 0 => rfl
  | n + 1 => by simp only [Rep4371.Native.packN, Model.packN, packN_eq f n]

theorem betaN_eq (j : ℕ) : Rep4371.Native.betaN j = Model.betaN j := by
  funext k
  unfold Rep4371.Native.betaN Model.betaN
  rw [popcN_eq, popcN_eq, bmaskN_eq]

theorem thetaRec_eq (a : ℕ) : ∀ n, Rep4371.Native.thetaRec n a = Model.thetaRec n a
  | 0 => rfl
  | n + 1 => by
    simp only [Rep4371.Native.thetaRec, Model.thetaRec, thetaRec_eq a n, packN_eq, betaN_eq,
      dualN_eq, combN_eq, bmaskN_eq]

theorem thetaN_eq (a : ℕ) : Rep4371.Native.thetaN a = Model.thetaN a := thetaRec_eq a 12

theorem pT_eq (c : ℕ) : pT c = (Rep4371.Native.pN c).toNat := by
  change (popc24 (wordT c) >>> 2) &&& 1 = _
  rw [popc24_eq, wordT_eq, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  have e : Rep4371.Native.pN c = (Rep4371.Native.popcN 24 (Model.wordN c) / 4 % 2 == 1) := by
    unfold Rep4371.Native.pN
    rw [wordN_eq]
  rw [e]
  have e4 : (2 : ℕ) ^ 2 = 4 := rfl
  rw [e4]
  rcases Nat.mod_two_eq_zero_or_one (Rep4371.Native.popcN 24 (Model.wordN c) / 4) with h | h <;>
    simp [h]

theorem oddCodeT_eq (c i : ℕ) : oddCodeT c i = Rep4371.Native.oddCode c i := by
  change c ^^^ selB (bitN (wordT c) i ^^^ pT c) 63 = _
  rw [bitN_eq, pT_eq, ← toNat_xor, selB_toNat, wordT_eq]
  unfold Rep4371.Native.oddCode
  rw [wordN_eq]

theorem octCodeT_eq {a : ℕ} (hw : Rep4371.Native.popcN 24 (Model.wordN a) = 8) (m : ℕ) :
    octCodeT a m = Native.octCodeG a m := by
  change a ^^^ selB ((popc24 (spreadT (wordT a) m) >>> 1) &&& 1) 63 = _
  rw [wordT_eq, spreadT_eq (by rw [flt_length_popcN]; exact hw), popc24_eq, Nat.and_one_is_mod,
    Nat.shiftRight_eq_div_pow, pow_one]
  unfold Native.octCodeG
  rw [wordN_eq]
  rcases Nat.mod_two_eq_zero_or_one
    (Rep4371.Native.popcN 24 (Native.spreadG (Model.wordN a) m) / 2) with h | h <;> simp [h, selB]

theorem testBit_packN (f : ℕ → Bool) (j : ℕ) :
    ∀ n, (Model.packN f n).testBit j = (decide (j < n) && f j)
  | 0 => by simp [Model.packN]
  | n + 1 => by
    simp only [Model.packN, Nat.testBit_or, testBit_packN f j n]
    by_cases h : j = n
    · subst h
      cases f j <;> simp
    · have e : (if f n = true then 2 ^ n else 0 : ℕ).testBit j = false := by
        split_ifs
        · rw [Nat.testBit_two_pow]
          exact decide_eq_false (Ne.symm h)
        · exact Nat.zero_testBit j
      rw [e, Bool.or_false]
      congr 1
      exact decide_eq_decide.2 (by omega)

theorem testBit_dualN (v j : ℕ) : (Model.dualN v).testBit j =
    (decide (j < 12) && Model.xorSum (fun i => v.testBit i && (Model.bmaskN j).testBit i) 24) := by
  unfold Model.dualN
  rw [testBit_packN, parN_eq]
  have e : (v &&& Model.bmaskN j).testBit = fun i => v.testBit i && (Model.bmaskN j).testBit i :=
    funext fun i => Nat.testBit_and _ _ _
  rw [e]

theorem testBit_combN' (m : ℕ → ℕ) (a j : ℕ) : ∀ n,
    (Model.combN m n a).testBit j = Model.xorSum (fun i => a.testBit i && (m i).testBit j) n
  | 0 => by simp [Model.combN, Model.xorSum]
  | n + 1 => by
    simp only [Model.combN, Model.xorSum, Nat.testBit_xor, testBit_combN' m a j n]
    cases a.testBit n <;> simp

theorem xorSum_single (i : ℕ) (b : Bool) : ∀ n,
    Model.xorSum (fun k => decide (i = k) && b) n = (decide (i < n) && b)
  | 0 => by simp [Model.xorSum]
  | n + 1 => by
    simp only [Model.xorSum, xorSum_single i b n]
    by_cases h : i = n
    · subst h
      simp
    · by_cases h' : i < n
      · rw [decide_eq_true h', decide_eq_true (by omega : i < n + 1), decide_eq_false h]
        simp
      · rw [decide_eq_false h', decide_eq_false (by omega : ¬ i < n + 1), decide_eq_false h]
        simp

theorem dualN_two_pow {i : ℕ} (hi : i < 24) (j : ℕ) :
    (Model.dualN (2 ^ i)).testBit j = (decide (j < 12) && (Model.bmaskN j).testBit i) := by
  rw [testBit_dualN]
  congr 1
  rw [xorSum_congr (g := fun k => decide (i = k) && (Model.bmaskN j).testBit i) fun k _ => by
    rw [Nat.testBit_two_pow]
    by_cases h : i = k
    · subst h
      simp
    · simp [h]]
  rw [xorSum_single, decide_eq_true hi, Bool.true_and]

theorem f12_du1 {DU1 : ℕ} (h3 : du1OK DU1 = true) {i : ℕ} (hi : i < 24) :
    f12 DU1 i = Model.dualN (2 ^ i) := by
  have := Nat.eq_of_beq_eq_true
    (recAll_left (P := fun i => Nat.beq (f12 DU1 i) (dualT (Nat.shiftLeft 1 i))) 24 h3 i hi)
  rw [this, dualT_eq, nshl, Nat.one_shiftLeft]

theorem dualL_eq {DU1 : ℕ} (h3 : du1OK DU1 = true) (v : ℕ) : dualL DU1 v = Model.dualN v := by
  have e : dualL DU1 v = Model.combN (fun i => Model.dualN (2 ^ i)) 24 v :=
    combN_loop _ _ v 24 fun i hi => f12_du1 h3 hi
  rw [e]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_combN', testBit_dualN]
  by_cases hj : j < 12
  · rw [decide_eq_true hj, Bool.true_and]
    exact xorSum_congr fun i hi => by rw [dualN_two_pow hi, decide_eq_true hj, Bool.true_and]
  · rw [decide_eq_false hj, Bool.false_and,
      xorSum_congr (g := fun _ => false) fun i hi => by
        rw [dualN_two_pow hi, decide_eq_false hj]
        simp]
    exact xorSum_false 24

theorem f12_lt (T i : ℕ) : f12 T i < 4096 := Nat.lt_succ_of_le Nat.and_le_right

theorem f12_th {TH : ℕ} (h1 : thOK TH = true) {a : ℕ} (ha : a < 4096) :
    f12 TH a = Rep4371.Native.thetaN a := by
  unfold thOK at h1
  generalize hN : nat_lit 4096 = N at h1
  have ha' : a < N := by rw [← hN]; exact ha
  have := Nat.eq_of_beq_eq_true
    (recAll_left (P := fun a => Nat.beq (f12 TH a) (thetaT a)) N h1 a ha')
  rw [this, thetaT_eq, thetaN_eq]

theorem thetaTab_at {a : ℕ} (ha : a < 4096) :
    (Native.thetaTab ())[a]! = Rep4371.Native.thetaN a := by
  unfold Native.thetaTab
  rw [getElem!_pos _ _ (by simpa using ha)]
  simp

set_option maxRecDepth 100000 in
theorem octTab_size {OCT : ℕ} (h : octOK OCT = true) : (Native.octTab ()).size = 759 := by
  unfold octOK at h
  generalize hN : nat_lit 4096 = N at h
  have hs := oST_spec OCT N
  unfold oST oStep at hs
  generalize Nat.rec (motive := fun _ => Bool × Nat) (true, nat_lit 0) _ N = s at h hs
  obtain ⟨ok, n⟩ := s
  obtain ⟨-, hn⟩ := Benes.andB_true h
  have hn' : n = 759 := Nat.eq_of_beq_eq_true hn
  obtain ⟨h1, -⟩ := hs
  simp only at h1
  have hN' : N = 4096 := hN.symm
  subst hN'
  have e1 : flt P8 4096 =
      flt (fun a => Rep4371.Native.popcN 24 (Rep4371.Native.wordN a) == 8) 4096 :=
    flt_congr fun a ha => popc_agree' ha
  rw [octTab_flt, List.size_toArray, ← e1]
  omega

theorem octTab_get {OCT : ℕ} (h2 : octOK OCT = true) {o : ℕ} (ho : o < 759) :
    (Native.octTab ())[o]! < 4096 ∧
      Rep4371.Native.popcN 24 (Model.wordN (Native.octTab ())[o]!) = 8 := by
  have hs := octTab_size h2
  rw [octTab_flt, List.size_toArray] at hs
  rw [octTab_flt, List.getElem!_toArray, getElem!_pos _ _ (by omega)]
  have hlen : o < (flt (fun a => Rep4371.Native.popcN 24 (Rep4371.Native.wordN a) == 8) 4096).length := by
    omega
  have hm := List.getElem_mem hlen
  unfold flt at hm ⊢
  rw [List.mem_filter, List.mem_range] at hm
  rw [← wordN_eq]
  exact ⟨hm.1, beq_iff_eq.1 hm.2⟩

theorem packN_lt' (f : ℕ → Bool) : ∀ n, Model.packN f n < 2 ^ n
  | 0 => by simp [Model.packN]
  | n + 1 => by
    simp only [Model.packN]
    refine Nat.or_lt_two_pow (lt_trans (packN_lt' f n)
      (Nat.pow_lt_pow_right (by norm_num) (by omega))) ?_
    split_ifs
    · exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    · exact Nat.two_pow_pos _

theorem dualN_lt' (v : ℕ) : Model.dualN v < 4096 := packN_lt' _ 12

theorem xor63_lt {c : ℕ} (hc : c < 4096) (P : Prop) [Decidable P] :
    c ^^^ (if P then 63 else 0) < 4096 :=
  Nat.xor_lt_two_pow (n := 12) hc (by split_ifs <;> norm_num)

theorem keyRec_eq {a : ℕ} (ha : a < 4096) (d : ℕ) : keyRec a d = a + 4096 * d := by
  change a ||| d <<< 12 = _
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by simpa using ha), Nat.shiftLeft_eq]
  ring

theorem keyRange_sound (TH OCT DU1 : ℕ) : ∀ d K lo, keyRange TH OCT DU1 d K lo = true →
    ∀ i < 2 ^ d, ∀ b < 32, K.testBit (32 * i + b) = (keyAtPos TH OCT DU1 (lo + i)).testBit b
  | 0, K, lo, h, i, hi, b, _ => by
    have h' : Nat.beq K (keyAtPos TH OCT DU1 lo) = true := h
    rw [Nat.eq_of_beq_eq_true h']
    obtain rfl : i = 0 := by simpa using hi
    simp
  | d + 1, K, lo, h, i, hi, b, hb => by
    have h' : andB (keyRange TH OCT DU1 d (Nat.land K (ones (Nat.mul (nat_lit 32)
        (Nat.shiftLeft (nat_lit 1) d)))) lo)
        (keyRange TH OCT DU1 d (Nat.shiftRight K (Nat.mul (nat_lit 32) (Nat.shiftLeft (nat_lit 1) d)))
          (Nat.add lo (Nat.shiftLeft (nat_lit 1) d))) = true := h
    obtain ⟨hA, hB⟩ := andB_true h'
    have eh : Nat.mul (nat_lit 32) (Nat.shiftLeft (nat_lit 1) d) = 32 * 2 ^ d := by
      rw [nmul, nshl, Nat.one_shiftLeft]
    have eh' : Nat.shiftLeft (nat_lit 1) d = 2 ^ d := by rw [nshl, Nat.one_shiftLeft]
    rw [eh] at hA hB
    rw [eh', nadd] at hB
    have hp : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ, Nat.mul_comm]
    rcases Nat.lt_or_ge i (2 ^ d) with hi' | hi'
    · have := keyRange_sound TH OCT DU1 d _ lo hA i hi' b hb
      rw [nland, Nat.testBit_and, SortAux.testBit_ones, decide_eq_true (by omega),
        Bool.and_true] at this
      exact this
    · have := keyRange_sound TH OCT DU1 d _ _ hB (i - 2 ^ d) (by omega) b hb
      rw [nshr, Nat.testBit_shiftRight] at this
      have e1 : 32 * 2 ^ d + (32 * (i - 2 ^ d) + b) = 32 * i + b := by omega
      have e2 : lo + 2 ^ d + (i - 2 ^ d) = lo + i := by omega
      rw [e1, e2] at this
      exact this

theorem testBit_keySlice (KT i k : ℕ) (hk : k < 524288) :
    (keySlice KT i).testBit k = KT.testBit (524288 * i + k) := by
  unfold keySlice
  rw [nland, nshr, Nat.testBit_and, Nat.testBit_shiftRight, SortAux.testBit_ones,
    decide_eq_true hk, Bool.and_true]
  have e : Nat.mul i (nat_lit 524288) = 524288 * i := Nat.mul_comm _ _
  rw [e]

theorem recAll_andB {P : ℕ → Bool} : ∀ n,
    Nat.rec (motive := fun _ => Bool) true (fun i ih => andB (P i) ih) n = true →
    ∀ i < n, P i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    obtain ⟨h1, h2⟩ := andB_true h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact recAll_andB n h2 i hi
    · exact h1

theorem keysOK_bits {TH OCT DU1 KT : ℕ} (h4 : keysOK TH OCT DU1 KT = true) {p : ℕ}
    (hp : p < 131072) {b : ℕ} (hb : b < 32) :
    KT.testBit (32 * p + b) = (keyAtPos TH OCT DU1 p).testBit b := by
  unfold keysOK at h4
  generalize hN : nat_lit 8 = N at h4
  have hlt : p / 16384 < N := by
    rw [← hN]
    exact (by omega : p / 16384 < 8)
  have hi := recAll_andB (P := fun i => keyRange TH OCT DU1 (nat_lit 14) (keySlice KT i)
    (Nat.mul i (nat_lit 16384))) N h4 (p / 16384) hlt
  have h14 : p % 16384 < 2 ^ (nat_lit 14) := (by omega : p % 16384 < 16384)
  have := keyRange_sound TH OCT DU1 (nat_lit 14) (keySlice KT (p / 16384))
    (Nat.mul (p / 16384) (nat_lit 16384)) hi (p % 16384) h14 b hb
  have e1 : Nat.mul (p / 16384) (nat_lit 16384) + p % 16384 = p :=
    (by omega : p / 16384 * 16384 + p % 16384 = p)
  rw [e1, testBit_keySlice _ _ _ (by omega)] at this
  rw [← this]
  congr 1
  omega

theorem testBit_keyRecAt' (KT p i : ℕ) (hi : i < 32) :
    (keyRecAt KT p).testBit i = KT.testBit (32 * p + i) := by
  unfold keyRecAt
  rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and, Nat.testBit_div_two_pow,
    Nat.add_comm]

theorem keyRecAt_mod {TH OCT DU1 KT : ℕ} (h4 : keysOK TH OCT DU1 KT = true) {p : ℕ}
    (hp : p < 131072) (hK : keyAtPos TH OCT DU1 p < 2 ^ 24) :
    keyRecAt KT p % 2 ^ 24 = keyAtPos TH OCT DU1 p := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_mod_two_pow]
  by_cases hk : k < 24
  · rw [decide_eq_true hk, Bool.true_and, testBit_keyRecAt' _ _ _ (by omega),
      keysOK_bits h4 hp (by omega)]
  · rw [decide_eq_false hk, Bool.false_and, Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hK (Nat.pow_le_pow_right (by decide) (by omega)))]

theorem keyAtPos_pair {TH OCT DU1 q : ℕ} (hq : q < 552) :
    keyAtPos TH OCT DU1 (xposK q) = keyRec (Native.keyAt (Native.thetaTab ()) q).1
      (Native.keyAt (Native.thetaTab ()) q).2 ∧
      (Native.keyAt (Native.thetaTab ()) q).1 < 4096 ∧
      (Native.keyAt (Native.thetaTab ()) q).2 < 4096 := by
  have ht := InitAux.pairTab_ok (q / 2) (by omega)
  have hx : xposK q = (if q % 2 = 0 then 114688 else 115712) +
      32 * (Native.pairTab ())[q / 2]!.1 + (Native.pairTab ())[q / 2]!.2 := by
    unfold xposK
    simp only [hq, ↓reduceIte]
  have hk : Native.keyAt (Native.thetaTab ()) q = (if q % 2 = 0 then 0 else 63,
      Rep4371.Native.dualN (2 ^ (Native.pairTab ())[q / 2]!.1 ||| 2 ^ (Native.pairTab ())[q / 2]!.2)) := by
    unfold Native.keyAt
    simp only [hq, ↓reduceIte]
  rw [hx, hk]
  generalize (Native.pairTab ())[q / 2]! = t at ht
  obtain ⟨t1, t2⟩ := t
  simp only at ht ⊢
  rcases Nat.mod_two_eq_zero_or_one q with h | h
  · simp only [h, ↓reduceIte]
    rw [keyAtPos_hi TH OCT DU1 (by omega) (by omega : 114688 + 32 * t1 + t2 - 114688 = 32 * t1 + t2),
      ite_eq_left (by omega)]
    have e1 : (32 * t1 + t2) / 32 % 32 = t1 := by omega
    have e2 : (32 * t1 + t2) % 32 = t2 := by omega
    have e3 : (32 * t1 + t2) / 1024 % 2 = 0 := by omega
    rw [e1, e2, e3, dualT_eq, dualN_eq]
    exact ⟨rfl, by norm_num, dualN_lt' _⟩
  · simp only [h, Nat.one_ne_zero, ↓reduceIte]
    rw [keyAtPos_hi TH OCT DU1 (by omega)
      (by omega : 115712 + 32 * t1 + t2 - 114688 = 1024 + 32 * t1 + t2), ite_eq_left (by omega)]
    have e1 : (1024 + 32 * t1 + t2) / 32 % 32 = t1 := by omega
    have e2 : (1024 + 32 * t1 + t2) % 32 = t2 := by omega
    have e3 : (1024 + 32 * t1 + t2) / 1024 % 2 = 1 := by omega
    rw [e1, e2, e3, dualT_eq, dualN_eq]
    exact ⟨rfl, by norm_num, dualN_lt' _⟩

theorem keyAtPos_odd {TH OCT DU1 q : ℕ} (h1 : thOK TH = true) (h3 : du1OK DU1 = true)
    (hq1 : 552 ≤ q) (hq2 : q < 49704) :
    keyAtPos TH OCT DU1 (xposK q) = keyRec (Native.keyAt (Native.thetaTab ()) q).1
      (Native.keyAt (Native.thetaTab ()) q).2 ∧
      (Native.keyAt (Native.thetaTab ()) q).1 < 4096 ∧
      (Native.keyAt (Native.thetaTab ()) q).2 < 4096 := by
  have hn : ¬ q < 552 := by omega
  have hx : xposK q = 32 * ((q - 552) / 24) + (q - 552) % 24 := by
    unfold xposK
    simp only [hn, hq2, ↓reduceIte]
  have hk : Native.keyAt (Native.thetaTab ()) q =
      (Rep4371.Native.oddCode (2 * ((q - 552) / 24)) ((q - 552) % 24),
        (Native.thetaTab ())[Rep4371.Native.oddCode (2 * ((q - 552) / 24)) ((q - 552) % 24)]! ^^^
          Rep4371.Native.dualN (2 ^ ((q - 552) % 24))) := by
    unfold Native.keyAt
    simp only [hn, hq2, ↓reduceIte]
  rw [hx, keyAtPos_lo TH OCT DU1 (by omega), hk]
  have e1 : (32 * ((q - 552) / 24) + (q - 552) % 24) % 32 = (q - 552) % 24 := by omega
  have e2 : (32 * ((q - 552) / 24) + (q - 552) % 24) / 32 = (q - 552) / 24 := by omega
  rw [e1, e2, ite_eq_left (by omega), oddCodeT_eq]
  have ha : Rep4371.Native.oddCode (2 * ((q - 552) / 24)) ((q - 552) % 24) < 4096 := by
    unfold Rep4371.Native.oddCode
    exact xor63_lt (by omega) _
  rw [f12_th h1 ha, thetaTab_at ha, f12_du1 h3 (by omega), dualN_eq]
  refine ⟨rfl, ha, Nat.xor_lt_two_pow (n := 12) ?_ (dualN_lt' _)⟩
  rw [← f12_th h1 ha]
  exact f12_lt _ _

theorem keyAtPos_oct {TH OCT DU1 q : ℕ} (h1 : thOK TH = true) (h2 : octOK OCT = true)
    (h3 : du1OK DU1 = true) (hq1 : 49704 ≤ q) (hq2 : q < 98280) :
    keyAtPos TH OCT DU1 (xposK q) = keyRec (Native.keyAt (Native.thetaTab ()) q).1
      (Native.keyAt (Native.thetaTab ()) q).2 ∧
      (Native.keyAt (Native.thetaTab ()) q).1 < 4096 ∧
      (Native.keyAt (Native.thetaTab ()) q).2 < 4096 := by
  have hn : ¬ q < 552 := by omega
  have hn' : ¬ q < 49704 := by omega
  have hx : xposK q = 65536 + (q - 49704) := by
    unfold xposK
    simp only [hn, hn', ↓reduceIte]
  have hk : Native.keyAt (Native.thetaTab ()) q =
      (Native.octCodeG (Native.octTab ())[(q - 49704) / 64]! (Native.evenTab ())[(q - 49704) % 64]!,
        (Native.thetaTab ())[Native.octCodeG (Native.octTab ())[(q - 49704) / 64]!
            (Native.evenTab ())[(q - 49704) % 64]!]! ^^^
          Rep4371.Native.dualN (Native.spreadG (Rep4371.Native.wordN (Native.octTab ())[(q - 49704) / 64]!)
            (Native.evenTab ())[(q - 49704) % 64]!)) := by
    unfold Native.keyAt
    simp only [hn, hn', ↓reduceIte]
  rw [hx, keyAtPos_mid TH OCT DU1 (by omega) (by omega), hk]
  have e : 65536 + (q - 49704) - 65536 = q - 49704 := by omega
  have ho : (q - 49704) / 64 < 759 := by omega
  obtain ⟨ha0, hw⟩ := octTab_get h2 ho
  rw [e, f12_octOK h2 ho, ← evenTab_eq ((q - 49704) % 64) (Nat.mod_lt _ (by norm_num)),
    octCodeT_eq hw, dualL_eq h3, wordT_eq,
    spreadT_eq (by rw [flt_length_popcN]; exact hw), ← wordN_eq]
  have hb : Native.octCodeG (Native.octTab ())[(q - 49704) / 64]!
      (Native.evenTab ())[(q - 49704) % 64]! < 4096 := by
    unfold Native.octCodeG
    exact xor63_lt ha0 _
  rw [f12_th h1 hb, thetaTab_at hb, dualN_eq]
  refine ⟨rfl, hb, Nat.xor_lt_two_pow (n := 12) ?_ (dualN_lt' _)⟩
  rw [← f12_th h1 hb]
  exact f12_lt _ _

theorem keyAtPos_xposK {TH OCT DU1 q : ℕ} (h1 : thOK TH = true) (h2 : octOK OCT = true)
    (h3 : du1OK DU1 = true) (hq : q < 98280) :
    keyAtPos TH OCT DU1 (xposK q) = keyRec (Native.keyAt (Native.thetaTab ()) q).1
      (Native.keyAt (Native.thetaTab ()) q).2 ∧
      (Native.keyAt (Native.thetaTab ()) q).1 < 4096 ∧
      (Native.keyAt (Native.thetaTab ()) q).2 < 4096 := by
  rcases Nat.lt_or_ge q 552 with hq1 | hq1
  · exact keyAtPos_pair hq1
  rcases Nat.lt_or_ge q 49704 with hq2 | hq2
  · exact keyAtPos_odd h1 h3 hq1 hq2
  · exact keyAtPos_oct h1 h2 h3 hq2 hq

end KeysOKAux

theorem keysOK_sound (TH OCT DU1 KT : Nat) (h1 : thOK TH = true) (h2 : octOK OCT = true)
    (h3 : du1OK DU1 = true) (h4 : keysOK TH OCT DU1 KT = true) :
    ∀ q < 98280, Native.keyAt (Native.thetaTab ()) q =
      (keyRecAt KT (xposK q) % 4096, keyRecAt KT (xposK q) / 4096 % 4096) := by
  intro q hq
  obtain ⟨hK, hA, hD⟩ := KeysOKAux.keyAtPos_xposK h1 h2 h3 hq
  have hx : xposK q < 131072 := InitAux.xposK_lt' hq
  rw [KeysOKAux.keyRec_eq hA] at hK
  have hm := KeysOKAux.keyRecAt_mod h4 hx (by rw [hK]; norm_num; omega)
  rw [hK] at hm
  generalize Native.keyAt (Native.thetaTab ()) q = k at hm hA hD
  obtain ⟨a, d⟩ := k
  simp only at hm hA hD
  norm_num at hm
  refine Prod.ext ?_ ?_
  · simp only
    omega
  · simp only
    omega

open InitAux in
theorem keysOK_pad {TH OCT DU1 KT : Nat} (h4 : keysOK TH OCT DU1 KT = true) {p : Nat}
    (hp : p < SX) (hn : ∀ q < 98280, xposK q ≠ p) {b : Nat} (hb : b < 24) :
    KT.testBit (32 * p + b) = false := by
  have hp' : p < 131072 := hp
  rw [KeysOKAux.keysOK_bits h4 hp' (by omega)]
  have hv : validX.testBit p = false := by
    cases h : validX.testBit p
    · rfl
    · obtain ⟨q, hq, e⟩ := xposK_of_mem h
      exact absurd e (hn q hq)
  rw [← Bool.not_eq_true, testBit_validX] at hv
  have hz : keyAtPos TH OCT DU1 p = 0 := by
    rcases Nat.lt_or_ge p 65536 with h1 | h1
    · rw [KeysOKAux.keyAtPos_lo TH OCT DU1 h1, ite_eq_right_iff]
      intro h2
      exact absurd (Or.inl ⟨h1, h2⟩) hv
    · rw [KeysOKAux.keyAtPos_hi TH OCT DU1 (by omega) rfl, ite_eq_right_iff]
      intro h2
      exfalso
      apply hv
      omega
  rw [hz, Nat.zero_testBit]

namespace KeysAux

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.Benes CFSG.KC.KDense.InitAux
  CFSG.KC.KDense.SortAux

theorem SX_val : SX = 131072 := rfl

theorem plane_fold {R : ℕ → ℕ} {f : ℕ → ℕ → Bool}
    (hR : ∀ c q, (R c).testBit q = (decide (q < SX) && f c q)) {c : ℕ} (hc : c < 12) {p : ℕ}
    (hp : p < SX) :
    (plane SX c (Nat.rec (motive := fun _ => ℕ) 0
      (fun b acc => Nat.lor acc (Nat.shiftLeft (R b) (Nat.mul b SX))) 12)).testBit p = f c p := by
  unfold plane
  simp only [nland, nshr, nmul, Nat.testBit_and, Nat.testBit_shiftRight, testBit_ones,
    decide_eq_true hp, Bool.and_true]
  rw [Bool.eq_iff_iff, testBit_foldOr (fun b => Nat.shiftLeft (R b) (b * SX))]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, testBit_shl, hR,
    Bool.and_eq_true, decide_eq_true_eq]
  rw [SX_val] at hp ⊢
  constructor
  · rintro ⟨j, hj, hk, hlt, hf⟩
    obtain rfl : j = c := by omega
    rwa [Nat.add_sub_cancel_left] at hf
  · intro hf
    exact ⟨c, hc, by omega, by omega, by rwa [Nat.add_sub_cancel_left]⟩

theorem keyPlane_bit {F : Fix} {KT : ℕ} (h5 : keyPlanesOK F KT = true) {b p : ℕ} (hb : b < 24)
    (hp : p < SX) : (keyPlane F b).testBit p = KT.testBit (32 * p + b) := by
  obtain ⟨hA, hD⟩ := Benes.andB_true h5
  have hA' := Nat.eq_of_beq_eq_true hA
  have hD' := Nat.eq_of_beq_eq_true hD
  unfold keyPlane
  rcases Nat.lt_or_ge b 12 with h | h
  · have e : Nat.blt b (nat_lit 12) = true := by simpa using h
    rw [e]
    dsimp only
    rw [hA']
    exact plane_fold (R := fun c => rawPlane KT 32 SX 17 0 c) (f := fun c q => KT.testBit (32 * q + c))
      (fun c q => testBit_rawPlane (by decide) SX_pow q) h hp
  · have e : Nat.blt b (nat_lit 12) = false := by
      cases hc : Nat.blt b (nat_lit 12)
      · rfl
      · have : b < 12 := by simpa using hc
        omega
    rw [e]
    dsimp only
    rw [hD']
    have := plane_fold (R := fun c => rawPlane KT 32 SX 17 0 (Nat.add c 12))
      (f := fun c q => KT.testBit (32 * q + (c + 12)))
      (fun c q => testBit_rawPlane (by decide) SX_pow q) (c := Nat.sub b 12)
      (by simp only [nsub]; omega) hp
    refine this.trans ?_
    rw [nsub, Nat.sub_add_cancel h]

theorem testBit_keyRecAt (KT p i : ℕ) (hi : i < 32) :
    (keyRecAt KT p).testBit i = KT.testBit (32 * p + i) := by
  unfold keyRecAt
  rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and, Nat.testBit_div_two_pow,
    Nat.add_comm]

@[expose] noncomputable def kStep (F : Fix) (NK : ℕ) : ℕ → ℕ × ℕ → ℕ × ℕ :=
  fun j ih => Prod.rec (motive := fun _ => Nat × Nat) (fun lt eq =>
    (fun x => (fun y => (Nat.lor lt (Nat.land eq (Nat.land (Nat.xor (ones SX) x) y)),
        Nat.land eq (Nat.xor (ones SX) (Nat.xor x y))))
      (Nat.land (Nat.shiftRight x (nat_lit 1)) (ones (Nat.sub SX (nat_lit 1)))))
    (netP SX (nat_lit 17) (nat_lit 1) NK (keyPlane F (Nat.sub (nat_lit 23) j)))) ih

@[expose] noncomputable def kST (F : Fix) (NK j : ℕ) : ℕ × ℕ :=
  Nat.rec (motive := fun _ => Nat × Nat) (nat_lit 0, ones SX) (kStep F NK) j

theorem kST_succ (F : Fix) (NK j : ℕ) : kST F NK (j + 1) = kStep F NK j (kST F NK j) := rfl

theorem keysDistinctOK_eq (F : Fix) (NK : ℕ) : keysDistinctOK F NK =
    andB (netOK (nat_lit 17) NK) (andB (Nat.beq (netP SX (nat_lit 17) (nat_lit 1) NK validX)
      (ones (nat_lit 98280)))
    (Prod.rec (motive := fun _ => Bool)
      (fun lt _ => Nat.beq (Nat.land lt (ones (nat_lit 98279))) (ones (nat_lit 98279)))
      (kST F NK (nat_lit 24)))) :=
  rfl

theorem prod_rec_bool (f : ℕ → ℕ → Bool) (s : ℕ × ℕ) :
    Prod.rec (motive := fun _ => Bool) f s = f s.1 s.2 := by
  cases s
  rfl

theorem keysDistinctOK_eq' (F : Fix) (NK : ℕ) : keysDistinctOK F NK =
    andB (netOK (nat_lit 17) NK) (andB (Nat.beq (netP SX (nat_lit 17) (nat_lit 1) NK validX)
      (ones (nat_lit 98280)))
    (Nat.beq (Nat.land (kST F NK 24).1 (ones (nat_lit 98279))) (ones (nat_lit 98279)))) := by
  rw [keysDistinctOK_eq]

@[expose] noncomputable def kD (KT NK : ℕ) (j r : ℕ) : ℕ :=
  ((keyRecAt KT (benesPerm 17 NK r)).testBit (23 - j)).toNat

theorem toNat_lt (a b : Bool) : decide (a.toNat < b.toNat) = (!a && b) := by
  cases a <;> cases b <;> rfl

theorem toNat_eq (a b : Bool) : decide (a.toNat = b.toNat) = (true ^^ (a ^^ b)) := by
  cases a <;> cases b <;> rfl

theorem kStep_bits {F : Fix} {KT NK : ℕ} (h5 : keyPlanesOK F KT = true) (hN : netOK 17 NK = true)
    {j : ℕ} (hj : j < 24) (s : ℕ × ℕ) {r : ℕ} (hr : r < SX - 1) :
    (kStep F NK j s).1.testBit r =
        (s.1.testBit r || (s.2.testBit r && decide (kD KT NK j r < kD KT NK j (r + 1)))) ∧
      (kStep F NK j s).2.testBit r = (s.2.testBit r && decide (kD KT NK j r = kD KT NK j (r + 1))) := by
  obtain ⟨lt, eq⟩ := s
  have hv := stagesValid_of_netOK hN
  have hbit : ∀ t, t < SX → (netP SX (nat_lit 17) (nat_lit 1) NK
      (keyPlane F (Nat.sub (nat_lit 23) j))).testBit t =
        (keyRecAt KT (benesPerm 17 NK t)).testBit (23 - j) := by
    intro t ht
    have hπ : benesPerm 17 NK t < SX := by
      rw [SX_pow] at ht ⊢
      exact benesPerm_lt hv ht
    rw [testBit_netP1 hN _ ht, keyPlane_bit h5 (by simp only [nsub]; omega) hπ,
      testBit_keyRecAt _ _ _ (by omega)]
    rfl
  unfold kStep
  dsimp only
  generalize hX : netP SX (nat_lit 17) (nat_lit 1) NK (keyPlane F (Nat.sub (nat_lit 23) j)) = X
    at hbit
  have h0 := hbit r (by omega)
  have h1 := hbit (1 + r) (by omega)
  have hr' : r < Nat.sub SX 1 := hr
  simp only [nlor, nland, nxor, nshr, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor,
    Nat.testBit_shiftRight, testBit_ones, decide_eq_true (by omega : r < SX), decide_eq_true hr',
    Bool.and_true, h0, h1]
  unfold kD
  rw [Nat.add_comm r 1]
  generalize (keyRecAt KT (benesPerm 17 NK r)).testBit (23 - j) = a
  generalize (keyRecAt KT (benesPerm 17 NK (1 + r))).testBit (23 - j) = b
  generalize lt.testBit r = l
  generalize eq.testBit r = e
  cases a <;> cases b <;> cases l <;> cases e <;> exact ⟨rfl, rfl⟩

end KeysAux

open KeysAux SortAux CFSG.KC.Benes InitAux CFSG.KC.MonsterConv.Perm in
theorem keysDistinct_sound (F : Fix) (KT NK : Nat) (h5 : keyPlanesOK F KT = true)
    (h6 : keysDistinctOK F NK = true) :
    ∀ p < 98280, ∀ q < 98280,
      keyRecAt KT (xposK p) % 2 ^ 24 = keyRecAt KT (xposK q) % 2 ^ 24 → p = q := by
  intro p hp q hq hpq
  rw [keysDistinctOK_eq'] at h6
  obtain ⟨hN, h6'⟩ := Benes.andB_true h6
  obtain ⟨hV, hL⟩ := Benes.andB_true h6'
  have hV' := Nat.eq_of_beq_eq_true hV
  have hL' := Nat.eq_of_beq_eq_true hL
  have hlex := lex_inv (M := SX - 1) (B := 2) (N := 24) (kD KT NK)
    (fun j _ r => Bool.toNat_lt _) (kST F NK)
    (fun r hr => by
      refine ⟨Nat.zero_testBit r, ?_⟩
      change (ones SX).testBit r = true
      rw [testBit_ones, decide_eq_true (by omega)])
    (fun j hj r hr => by
      rw [kST_succ]
      exact kStep_bits h5 hN hj _ hr) 24 le_rfl
  have hinc : ∀ r, r + 1 < 98280 → lexV (kD KT NK) 2 24 r < lexV (kD KT NK) 2 24 (r + 1) := by
    intro r hr
    have h1 := (hlex r (by rw [SX_val]; omega)).1
    have h2 : (Nat.land (kST F NK 24).1 (ones 98279)).testBit r = (ones 98279).testBit r := by
      rw [hL']
    rw [nland, Nat.testBit_and, testBit_ones, decide_eq_true (by omega : r < 98279),
      Bool.and_true, h1] at h2
    exact of_decide_eq_true h2
  obtain ⟨hp1, hp2⟩ := validX_perm hN hV' hp
  obtain ⟨hq1, hq2⟩ := validX_perm hN hV' hq
  have hdig : ∀ j < 24, kD KT NK j (benesInv 17 NK (xposK p)) =
      kD KT NK j (benesInv 17 NK (xposK q)) := by
    intro j hj
    unfold kD
    rw [hp2, hq2]
    have := congrArg (fun x => x.testBit (23 - j)) hpq
    simp only [Nat.testBit_mod_two_pow, decide_eq_true (by omega : 23 - j < 24), Bool.true_and]
      at this
    rw [this]
  have e := lexV_inj hinc _ _ hp1 hq1 (lexV_congr (kD KT NK) 2 24 hdig)
  have e2 : xposK p = xposK q := by rw [← hp2, e, hq2]
  exact xposK_inj hp hq e2

theorem keys_sound (F : Fix) (KT TH OCT DU1 NK : Nat) (h1 : thOK TH = true) (h2 : octOK OCT = true)
    (h3 : du1OK DU1 = true) (h4 : keysOK TH OCT DU1 KT = true) (h5 : keyPlanesOK F KT = true)
    (h6 : keysDistinctOK F NK = true) :
    (∀ p < 98280, (Native.keyAt (Native.thetaTab ()) p).1 < 4096 ∧
      (Native.keyAt (Native.thetaTab ()) p).2 < 4096) ∧
    ∀ p < 98280, ∀ q < 98280, Native.keyAt (Native.thetaTab ()) p =
      Native.keyAt (Native.thetaTab ()) q → p = q := by
  have hk := keysOK_sound TH OCT DU1 KT h1 h2 h3 h4
  refine ⟨fun p hp => ?_, fun p hp q hq e => ?_⟩
  · rw [hk p hp]
    exact ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩
  · rw [hk p hp, hk q hq, Prod.mk.injEq] at e
    refine keysDistinct_sound F KT NK h5 h6 p hp q hq ?_
    obtain ⟨e1, e2⟩ := e
    have e24 : (2 : Nat) ^ 24 = 16777216 := rfl
    rw [e24]
    omega

end CFSG.KC.KDense

end
