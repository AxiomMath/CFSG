module

public import Certificates.Data.Kernel.Co2Kill
public import CFSG.Certificates.Kernel.HOrbSound
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases
import CFSG.Certificates.Kernel.LceSP.Main
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

namespace CFSG.Certificates.Co2Kill

open CFSG.KC CFSG.KC.LceS CFSG.KC.HOrb CFSG.KC.Co2K CFSG.Certificates.LCE CFSG.Certificates.HO

@[expose] noncomputable def dec7 (X : ℕ) : Matrix (Fin 10) (Fin 10) (ZMod 7) :=
  fun i j => ((Nat.land (Nat.shiftRight X (12 * (10 * i.val + j.val))) 4095 : ℕ) : ZMod 7)

def lane (i X : ℕ) : ℕ := X / 4096 ^ i % 4096

def lsum (f : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, f i * 4096 ^ i

theorem lane_lt (i X : ℕ) : lane i X < 4096 := Nat.mod_lt _ (by norm_num)

theorem four096_pow (i : ℕ) : (4096 : ℕ) ^ i = 2 ^ (12 * i) := by
  rw [pow_mul]
  norm_num

theorem lane_concat {A B p i : ℕ} (hA : A < 4096 ^ p) :
    lane i (A + B * 4096 ^ p) = if i < p then lane i A else lane (i - p) B := by
  unfold lane
  split_ifs with hi
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hi
    have e : B * 4096 ^ (i + d + 1) = 4096 ^ i * (4096 * (B * 4096 ^ d)) := by ring
    rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hi)
    have e : (A + B * 4096 ^ p) / 4096 ^ (p + j) = B / 4096 ^ j := by
      rw [pow_add, ← Nat.div_div_eq_div_mul, Nat.mul_comm B, Nat.add_mul_div_left _ _ (by positivity),
        Nat.div_eq_of_lt hA, Nat.zero_add]
    rw [e, Nat.add_sub_cancel_left]

theorem lane_mod {y p j : ℕ} (hj : j < p) : lane j (y % 4096 ^ p) = lane j y := by
  have h := lane_concat (B := y / 4096 ^ p) (i := j) (Nat.mod_lt y (by positivity : 0 < 4096 ^ p))
  rw [Nat.mod_add_div'] at h
  simp only [hj, ↓reduceIte] at h
  exact h.symm

theorem lane_div (y p j : ℕ) : lane j (y / 4096 ^ p) = lane (p + j) y := by
  unfold lane
  rw [Nat.div_div_eq_div_mul, ← pow_add]

theorem lsum_succ (f : ℕ → ℕ) (n : ℕ) : lsum f (n + 1) = lsum f n + f n * 4096 ^ n :=
  Finset.sum_range_succ _ _

theorem lsum_spec (f : ℕ → ℕ) : ∀ n, (∀ i < n, f i < 4096) →
    lsum f n < 4096 ^ n ∧ ∀ i < n, lane i (lsum f n) = f i
  | 0, _ => ⟨by simp [lsum], fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hf => by
    obtain ⟨hlt, hl⟩ := lsum_spec f n fun i hi => hf i (by omega)
    have hn := hf n (by omega)
    rw [lsum_succ]
    refine ⟨?_, fun i hi => ?_⟩
    · calc lsum f n + f n * 4096 ^ n < 4096 ^ n + f n * 4096 ^ n := by omega
        _ = (f n + 1) * 4096 ^ n := by ring
        _ ≤ 4096 * 4096 ^ n := Nat.mul_le_mul_right _ (by omega)
        _ = 4096 ^ (n + 1) := by ring
    · rw [lane_concat hlt]
      split_ifs with h
      · exact hl i h
      · have : i = n := by omega
        subst this
        simp [lane, Nat.mod_eq_of_lt hn]

theorem lsum_lane (X : ℕ) : ∀ n, lsum (fun i => lane i X) n = X % 4096 ^ n
  | 0 => by simp [lsum, Nat.mod_one]
  | n + 1 => by
    rw [lsum_succ, lsum_lane X n, Nat.mod_pow_succ]
    unfold lane
    ring

theorem lsum_congr {f g : ℕ → ℕ} {n : ℕ} (h : ∀ i < n, f i = g i) : lsum f n = lsum g n :=
  Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.mp hi)]

theorem eq_lsum {X n : ℕ} {f : ℕ → ℕ} (hX : X < 4096 ^ n) (h : ∀ i < n, lane i X = f i) :
    X = lsum f n := by
  rw [← lsum_congr h, lsum_lane, Nat.mod_eq_of_lt hX]

theorem lsum_add (f g : ℕ → ℕ) (n : ℕ) : lsum f n + lsum g n = lsum (fun i => f i + g i) n := by
  unfold lsum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => (add_mul _ _ _).symm

theorem lsum_mul (f : ℕ → ℕ) (n c : ℕ) : lsum f n * c = lsum (fun i => f i * c) n := by
  unfold lsum
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem lsum_sub {f g : ℕ → ℕ} {n : ℕ} (h : ∀ i < n, g i ≤ f i) :
    lsum f n - lsum g n = lsum (fun i => f i - g i) n := by
  have : lsum f n = lsum (fun i => f i - g i) n + lsum g n := by
    rw [lsum_add]
    exact lsum_congr fun i hi => (Nat.sub_add_cancel (h i hi)).symm
  omega

theorem lsum_blocks (f : ℕ → ℕ) : ∀ n, lsum f (10 * n) =
    ∑ i ∈ Finset.range n, (∑ j ∈ Finset.range 10, f (10 * i + j) * 4096 ^ j) * 4096 ^ (10 * i)
  | 0 => by simp [lsum]
  | n + 1 => by
    rw [Finset.sum_range_succ, ← lsum_blocks f n]
    unfold lsum
    rw [show 10 * (n + 1) = 10 * n + 10 by ring, Finset.sum_range_add, Finset.sum_mul,
      Nat.add_left_cancel_iff]
    exact Finset.sum_congr rfl fun j _ => by ring

theorem lane_land (i x y : ℕ) : lane i (x &&& y) = lane i x &&& lane i y := by
  unfold lane
  have h : (4096 : ℕ) = 2 ^ 12 := by norm_num
  rw [four096_pow, h, Nat.and_div_two_pow, Nat.and_mod_two_pow]

theorem land_mask {c n : ℕ} (m : ℕ → ℕ) (hc : c < 4096 ^ n) (hm : ∀ i < n, lane i c = m i)
    (v : ℕ) : v &&& c = lsum (fun i => lane i v &&& m i) n :=
  eq_lsum (lt_of_le_of_lt Nat.and_le_right hc) fun i hi => by rw [lane_land, hm i hi]

theorem lane_shr3 (i v : ℕ) : lane i (v >>> 3) = v / 4096 ^ i / 8 % 4096 := by
  have h : v >>> 3 = v / 8 := by rw [Nat.shiftRight_eq_div_pow]
  unfold lane
  rw [h, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem lane_shr3_511 (i v : ℕ) : lane i (v >>> 3) &&& 511 = lane i v / 8 := by
  rw [lane_shr3, (Nat.and_two_pow_sub_one_eq_mod _ 9 : _ &&& 511 = _ % 512)]
  unfold lane
  generalize v / 4096 ^ i = x
  omega

theorem lane_shr3_1 (i v : ℕ) : lane i (v >>> 3) &&& 1 = lane i v / 8 % 2 := by
  rw [lane_shr3, (Nat.and_two_pow_sub_one_eq_mod _ 1 : _ &&& 1 = _ % 2)]
  unfold lane
  generalize v / 4096 ^ i = x
  omega

theorem L7_spec : L7 < 4096 ^ 100 ∧ ∀ i < 100, lane i L7 = 7 := by decide

theorem L1FF_spec : L1FF < 4096 ^ 100 ∧ ∀ i < 100, lane i L1FF = 511 := by decide

theorem L1_spec : L1 < 4096 ^ 100 ∧ ∀ i < 100, lane i L1 = 1 := by decide

theorem COLM_spec : COLM < 4096 ^ 100 ∧
    ∀ i < 100, lane i COLM = if i % 10 = 0 then 4095 else 0 := by decide

theorem P1200_eq : P1200 = 4096 ^ 100 := by decide

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

def f7 (y : ℕ) : ℕ := y % 8 + y / 8

theorem fold7_eq (v : ℕ) : fold7 v = lsum (fun i => f7 (lane i v)) 100 := by
  unfold fold7
  rw [strictN_eq]
  change (v &&& L7) + ((v >>> 3) &&& L1FF) = _
  rw [land_mask (fun _ => 7) L7_spec.1 L7_spec.2, land_mask (fun _ => 511) L1FF_spec.1 L1FF_spec.2,
    lsum_add]
  refine lsum_congr fun i _ => ?_
  rw [lane_shr3_511, (Nat.and_two_pow_sub_one_eq_mod _ 3 : _ &&& 7 = _ % 8)]
  rfl

theorem f7_lt {y : ℕ} (hy : y < 4096) : f7 y < 4096 := by
  unfold f7
  omega

theorem fold7_lsum {g : ℕ → ℕ} (hg : ∀ i < 100, g i < 4096) :
    fold7 (lsum g 100) = lsum (fun i => f7 (g i)) 100 := by
  rw [fold7_eq]
  exact lsum_congr fun i hi => by rw [(lsum_spec g 100 hg).2 i hi]

theorem red_lane (y : ℕ) (hy : y < 4096) :
    f7 (f7 (f7 (f7 (f7 y)))) ≤ 7 ∧
      f7 (f7 (f7 (f7 (f7 y)))) - (f7 (f7 (f7 (f7 (f7 y)))) + 1) / 8 % 2 * 7 = y % 7 := by
  have s1 : ∀ y, y < 4096 → f7 y < 519 := fun y h => by unfold f7; omega
  have s2 : ∀ y, y < 519 → f7 y < 72 := fun y h => by unfold f7; omega
  have s3 : ∀ y, y < 72 → f7 y < 16 := fun y h => by unfold f7; omega
  have s4 : ∀ y, y < 16 → f7 y < 9 := fun y h => by unfold f7; omega
  have s5 : ∀ y, y < 9 → f7 y ≤ 7 := fun y h => by unfold f7; omega
  have hm : ∀ y, f7 y % 7 = y % 7 := fun y => by unfold f7; omega
  have hb := s5 _ (s4 _ (s3 _ (s2 _ (s1 _ hy))))
  have hmod : f7 (f7 (f7 (f7 (f7 y)))) % 7 = y % 7 := by rw [hm, hm, hm, hm, hm]
  refine ⟨hb, ?_⟩
  generalize f7 (f7 (f7 (f7 (f7 y)))) = g at hb hmod ⊢
  interval_cases g <;> omega

theorem red7_eq (x : ℕ) : red7 x = lsum (fun i => lane i x % 7) 100 := by
  have h0 : ∀ i < 100, lane i x < 4096 := fun i _ => lane_lt i x
  have e2 : fold7 (fold7 x) = lsum (fun i => f7 (f7 (lane i x))) 100 := by
    rw [fold7_eq x, fold7_lsum fun i hi => f7_lt (h0 i hi)]
  have e3 : fold7 (fold7 (fold7 x)) = lsum (fun i => f7 (f7 (f7 (lane i x)))) 100 := by
    rw [e2, fold7_lsum fun i hi => f7_lt (f7_lt (h0 i hi))]
  have e4 : fold7 (fold7 (fold7 (fold7 x))) = lsum (fun i => f7 (f7 (f7 (f7 (lane i x))))) 100 := by
    rw [e3, fold7_lsum fun i hi => f7_lt (f7_lt (f7_lt (h0 i hi)))]
  have e5 : fold7 (fold7 (fold7 (fold7 (fold7 x)))) =
      lsum (fun i => f7 (f7 (f7 (f7 (f7 (lane i x)))))) 100 := by
    rw [e4, fold7_lsum fun i hi => f7_lt (f7_lt (f7_lt (f7_lt (h0 i hi))))]
  unfold red7
  rw [e5, strictN_eq]
  set g : ℕ → ℕ := fun i => f7 (f7 (f7 (f7 (f7 (lane i x))))) with hg
  have hr : ∀ i < 100, g i ≤ 7 ∧ g i - (g i + 1) / 8 % 2 * 7 = lane i x % 7 :=
    fun i _ => red_lane _ (lane_lt i x)
  change lsum g 100 - (((lsum g 100 + L1) >>> 3) &&& L1) * 7 = _
  have hL1 : L1 = lsum (fun _ => 1) 100 := eq_lsum L1_spec.1 L1_spec.2
  have hS : lsum g 100 + L1 = lsum (fun i => g i + 1) 100 := by rw [hL1, lsum_add]
  have hm : ((lsum g 100 + L1) >>> 3) &&& L1 = lsum (fun i => (g i + 1) / 8 % 2) 100 := by
    rw [land_mask (fun _ => 1) L1_spec.1 L1_spec.2]
    refine lsum_congr fun i hi => ?_
    rw [lane_shr3_1, hS, (lsum_spec _ 100 fun j hj => by have := (hr j hj).1; omega).2 i hi]
  rw [hm, lsum_mul, lsum_sub fun i hi => by have := (hr i hi).1; omega]
  exact lsum_congr fun i hi => (hr i hi).2

theorem wf7_iff (X : ℕ) : wf7 X = true ↔ X < 4096 ^ 100 ∧ ∀ i < 100, lane i X < 7 := by
  unfold wf7
  rw [andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, P1200_eq, red7_eq]
  constructor
  · rintro ⟨hX, he⟩
    refine ⟨hX, fun i hi => ?_⟩
    have h := (lsum_spec (fun i => lane i X % 7) 100 fun j _ =>
      lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)).2 i hi
    rw [he] at h
    rw [h]
    exact Nat.mod_lt _ (by norm_num)
  · rintro ⟨hX, hl⟩
    refine ⟨hX, ?_⟩
    rw [lsum_congr (g := fun i => lane i X) fun i hi => Nat.mod_eq_of_lt (hl i hi), lsum_lane,
      Nat.mod_eq_of_lt hX]

theorem shr_and_eq_lane (X k : ℕ) : X >>> (12 * k) &&& 4095 = lane k X := by
  unfold lane
  rw [Nat.shiftRight_eq_div_pow, four096_pow]
  exact Nat.and_two_pow_sub_one_eq_mod _ 12

theorem dec7_apply (X : ℕ) (i j : Fin 10) :
    dec7 X i j = ((lane (10 * i.val + j.val) X : ℕ) : ZMod 7) := by
  unfold dec7
  change ((X >>> (12 * (10 * i.val + j.val)) &&& 4095 : ℕ) : ZMod 7) = _
  rw [shr_and_eq_lane]

theorem row7_eq (B k : ℕ) : row7 B k = lsum (fun j => lane (10 * k + j) B) 10 := by
  unfold row7
  change B >>> (120 * k) &&& M120 = _
  have hM : M120 = 2 ^ 120 - 1 := by decide
  have h2 : (2 : ℕ) ^ 120 = 4096 ^ 10 := by norm_num
  have h3 : (2 : ℕ) ^ (120 * k) = 4096 ^ (10 * k) := by
    rw [four096_pow]
    congr 1
    ring
  rw [hM, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, h2, h3]
  exact eq_lsum (Nat.mod_lt _ (by positivity)) fun j hj => by rw [lane_mod hj, lane_div]

theorem col7_eq (A k : ℕ) :
    col7 A k = ∑ i ∈ Finset.range 10, lane (10 * i + k) A * 4096 ^ (10 * i) := by
  unfold col7
  change A >>> (12 * k) &&& COLM = _
  rw [land_mask _ COLM_spec.1 COLM_spec.2, show (100 : ℕ) = 10 * 10 from rfl, lsum_blocks]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [Finset.sum_range_succ', Finset.sum_eq_zero fun j hj => ?_]
  · rw [Nat.shiftRight_eq_div_pow, ← four096_pow, lane_div]
    have h0 : (10 * i + 0) % 10 = 0 := by omega
    simp only [h0, ↓reduceIte, pow_zero, mul_one, zero_add]
    rw [Nat.add_zero, Nat.add_comm k, (Nat.and_two_pow_sub_one_eq_mod _ 12 : _ &&& 4095 = _ % 4096),
      Nat.mod_eq_of_lt (lane_lt _ _)]
  · have hj' := Finset.mem_range.mp hj
    have h1 : (10 * i + (j + 1)) % 10 ≠ 0 := by omega
    simp only [h1, ↓reduceIte, Nat.and_zero, zero_mul]

theorem rowcol (A B k : ℕ) : row7 B k * col7 A k = ∑ i ∈ Finset.range 10, ∑ j ∈ Finset.range 10,
    lane (10 * i + k) A * lane (10 * k + j) B * 4096 ^ (10 * i + j) := by
  rw [row7_eq, col7_eq]
  unfold lsum
  rw [Finset.sum_mul_sum, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem mul7_acc (A B : ℕ) : ∀ n, Nat.rec (motive := fun _ => ℕ) 0
    (fun k acc => CFSG.KC.Loop.strictN acc (fun s => Nat.add s (Nat.mul (row7 B k) (col7 A k)))) n =
      ∑ k ∈ Finset.range n, row7 B k * col7 A k
  | 0 => rfl
  | n + 1 => by
    rw [Finset.sum_range_succ, ← mul7_acc A B n]
    change CFSG.KC.Loop.strictN _ (fun s => Nat.add s (Nat.mul (row7 B n) (col7 A n))) = _
    rw [strictN_eq]
    rfl

theorem mul7_sound {A B : ℕ} (hA : wf7 A = true) (hB : wf7 B = true) :
    wf7 (mul7 A B) = true ∧ dec7 (mul7 A B) = dec7 A * dec7 B := by
  rw [wf7_iff] at hA hB
  set C : ℕ → ℕ → ℕ := fun i j => ∑ k ∈ Finset.range 10, lane (10 * i + k) A * lane (10 * k + j) B
    with hC
  have hCl : ∀ i < 10, ∀ j < 10, C i j < 4096 := by
    intro i hi j hj
    have hle : C i j ≤ ∑ _k ∈ Finset.range 10, 36 := Finset.sum_le_sum fun k hk => by
      have hk' := Finset.mem_range.mp hk
      have a := hA.2 (10 * i + k) (by omega)
      have b := hB.2 (10 * k + j) (by omega)
      exact Nat.mul_le_mul (by omega : _ ≤ 6) (by omega : _ ≤ 6)
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hle
    omega
  set f : ℕ → ℕ := fun l => C (l / 10) (l % 10) with hf
  have hfl : ∀ l < 100, f l < 4096 := fun l hl => hCl _ (by omega) _ (by omega)
  have hsum : (∑ k ∈ Finset.range 10, row7 B k * col7 A k) = lsum f 100 := by
    rw [show (100 : ℕ) = 10 * 10 from rfl, lsum_blocks]
    simp only [rowcol]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    have e1 : (10 * i + j) / 10 = i := by omega
    have e2 : (10 * i + j) % 10 = j := by omega
    simp only [hf, e1, e2, hC, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hmul : mul7 A B = lsum (fun l => f l % 7) 100 := by
    have e : mul7 A B = red7 (∑ k ∈ Finset.range 10, row7 B k * col7 A k) :=
      congrArg red7 (mul7_acc A B 10)
    rw [e, hsum, red7_eq]
    exact lsum_congr fun l hl => by rw [(lsum_spec f 100 hfl).2 l hl]
  have hlt : ∀ l < 100, f l % 7 < 4096 := fun l _ =>
    lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)
  have hlane := lsum_spec (fun l => f l % 7) 100 hlt
  refine ⟨(wf7_iff _).2 ⟨by rw [hmul]; exact hlane.1, fun l hl => ?_⟩, ?_⟩
  · rw [hmul, hlane.2 l hl]
    exact Nat.mod_lt _ (by norm_num)
  · ext i j
    have hi := i.isLt
    have hj := j.isLt
    rw [dec7_apply, hmul, hlane.2 _ (by omega), Matrix.mul_apply]
    simp only [dec7_apply]
    have e1 : (10 * i.val + j.val) / 10 = i.val := by omega
    have e2 : (10 * i.val + j.val) % 10 = j.val := by omega
    simp only [hf, e1, e2, hC, ZMod.natCast_mod]
    push_cast
    exact (Fin.sum_univ_eq_sum_range (fun k => (lane (10 * i.val + k) A : ZMod 7) *
      (lane (10 * k + j.val) B : ZMod 7)) 10).symm

theorem dec7_inj {A B : ℕ} (hA : wf7 A = true) (hB : wf7 B = true) (h : dec7 A = dec7 B) :
    A = B := by
  rw [wf7_iff] at hA hB
  have hl : ∀ l < 100, lane l A = lane l B := by
    intro l hl
    have h1 := congrFun (congrFun h ⟨l / 10, by omega⟩) ⟨l % 10, by omega⟩
    rw [dec7_apply, dec7_apply] at h1
    dsimp only at h1
    rw [show 10 * (l / 10) + l % 10 = l by omega, ZMod.natCast_eq_natCast_iff',
      Nat.mod_eq_of_lt (hA.2 l hl), Nat.mod_eq_of_lt (hB.2 l hl)] at h1
    exact h1
  calc A = lsum (fun i => lane i B) 100 := eq_lsum hA.1 hl
    _ = B := (eq_lsum hB.1 fun i _ => rfl).symm

theorem entOK_mono {e b b' n n' : ℕ} (h : entOK e b n = true) (hb : b ≤ b') (hn : n ≤ n') :
    entOK e b' n' = true := by
  obtain ⟨h1, h2, h3⟩ := (entOK_iff _ _ _).1 h
  exact (entOK_iff _ _ _).2 ⟨h1, le_trans h2 hn, fun i hi => lt_of_lt_of_le (h3 i hi) hb⟩

theorem wLen_le {e b n : ℕ} (h : entOK e b n = true) : wLen e ≤ n :=
  ((entOK_iff _ _ _).1 h).2.1

theorem entOK_zero (b : ℕ) : entOK 0 b 0 = true := by
  have h0 : wLen 0 = 0 := by decide
  refine (entOK_iff _ _ _).2 ⟨by decide, by decide, fun i hi => ?_⟩
  omega

theorem catEnt_spec {G : Type*} [Group G] (gen : ℕ → G) {e f b n1 n2 : ℕ}
    (he : entOK e b n1 = true) (hf : entOK f b n2 = true) (hn : n1 + n2 < 1024) :
    entOK (Co2K.catEnt e f) b (n1 + n2) = true ∧ wLen (Co2K.catEnt e f) = wLen e + wLen f ∧
      bval gen (wWord (Co2K.catEnt e f)) (wLen (Co2K.catEnt e f)) =
        bval gen (wWord e) (wLen e) * bval gen (wWord f) (wLen f) := by
  obtain ⟨hlt, hle, hLe⟩ := (entOK_iff _ _ _).1 he
  obtain ⟨hWf, hlf, hLf⟩ := (entOK_iff _ _ _).1 hf
  have hWe : wWord e < 256 ^ wLen e := by rwa [two_pow_eight_mul] at hlt
  rw [two_pow_eight_mul] at hWf
  have hW : (wWord e ||| wWord f <<< (8 * wLen e)) = wWord e + wWord f * 256 ^ wLen e := by
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hlt, Nat.shiftLeft_eq, two_pow_eight_mul,
      Nat.add_comm]
  have hc : Co2K.catEnt e f =
      4 * (wLen e + wLen f) + (wWord e + wWord f * 256 ^ wLen e) <<< 12 := by
    rw [← hW]
    rfl
  have hn' : wLen e + wLen f < 1024 := by omega
  rw [hc]
  refine ⟨?_, wLen_mk _ _ hn', by rw [wLen_mk _ _ hn', wWord_mk _ _ hn']; exact bval_concat gen hWe⟩
  rw [entOK_iff, wLen_mk _ _ hn', wWord_mk _ _ hn']
  refine ⟨?_, by omega, fun i hi => ?_⟩
  · rw [two_pow_eight_mul]
    calc wWord e + wWord f * 256 ^ wLen e < 256 ^ wLen e + wWord f * 256 ^ wLen e := by omega
      _ = (wWord f + 1) * 256 ^ wLen e := by ring
      _ ≤ 256 ^ wLen f * 256 ^ wLen e := Nat.mul_le_mul_right _ (by omega)
      _ = 256 ^ (wLen e + wLen f) := by ring
  · rw [wLet_eq, byte_concat hWe]
    split_ifs with h
    · have := hLe i h
      rwa [wLet_eq] at this
    · have := hLf (i - wLen e) (by omega)
      rwa [wLet_eq] at this

theorem letEnt_spec {G : Type*} [Group G] (gen : ℕ → G) {c : ℕ} (hc : c < 254) :
    entOK (Co2K.letEnt c) 254 1 = true ∧ wLen (Co2K.letEnt c) = 1 ∧
      bval gen (wWord (Co2K.letEnt c)) (wLen (Co2K.letEnt c)) = letV gen c := by
  have e : Co2K.letEnt c = 4 * 1 + c <<< 12 := rfl
  have h1 : wLen (4 * 1 + c <<< 12) = 1 := wLen_mk _ _ (by norm_num)
  have h2 : wWord (4 * 1 + c <<< 12) = c := wWord_mk _ _ (by norm_num)
  rw [e]
  refine ⟨?_, h1, by rw [h1, h2, bval_one gen (by omega)]⟩
  rw [entOK_iff, h1, h2]
  refine ⟨by norm_num; omega, le_rfl, fun i hi => ?_⟩
  · rw [wLet_eq]
    have : i = 0 := by omega
    subst this
    simp only [pow_zero, Nat.div_one]
    omega

theorem invEnt_spec {G : Type*} [Group G] (gen : ℕ → G) {e n : ℕ} (he : entOK e 254 n = true)
    (hn : n ≤ 1023) :
    entOK (invEnt e) 254 n = true ∧ wLen (invEnt e) = wLen e ∧
      bval gen (wWord (invEnt e)) (wLen (invEnt e)) = (bval gen (wWord e) (wLen e))⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := bval_invEnt gen (entOK_mono he le_rfl hn)
  obtain ⟨a1, -, a3⟩ := (entOK_iff _ _ _).1 h1
  refine ⟨(entOK_iff _ _ _).2 ⟨a1, by rw [h2]; exact wLen_le he, a3⟩, h2, h3⟩

theorem sliceEnt_eq (e lo cnt : ℕ) :
    Co2K.sliceEnt e lo cnt = 4 * cnt + (wWord e / 256 ^ lo % 256 ^ cnt) <<< 12 := by
  change 4 * cnt + ((wWord e >>> (8 * lo)) &&& ((1 <<< (8 * cnt)) - 1)) <<< 12 = _
  rw [Nat.shiftLeft_eq 1, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
    two_pow_eight_mul, two_pow_eight_mul]

theorem gw_spec {G : Type*} [Group G] (gen : ℕ → G) {GW : ℕ → ℕ} {k : ℕ}
    (hk : gwShape GW k = true) :
    entOK (Co2K.sigma GW k) 254 15 = true ∧ entOK (Co2K.sigInv GW k) 254 15 = true ∧
      bval gen (wWord (Co2K.sigInv GW k)) (wLen (Co2K.sigInv GW k)) =
        (bval gen (wWord (Co2K.sigma GW k)) (wLen (Co2K.sigma GW k)))⁻¹ ∧
      bval gen (wWord (GW k)) (wLen (GW k)) =
        (bval gen (wWord (Co2K.sigma GW k)) (wLen (Co2K.sigma GW k)))⁻¹ * gen 0 *
          bval gen (wWord (Co2K.sigma GW k)) (wLen (Co2K.sigma GW k)) := by
  unfold gwShape at hk
  simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq] at hk
  obtain ⟨hent, hodd, hmid, hsig⟩ := hk
  obtain ⟨hWlt, hn, hl⟩ := (entOK_iff _ _ _).1 hent
  set n := wLen (GW k) with hndef
  set W := wWord (GW k) with hWdef
  have hgh : Co2K.gHalf GW k = n / 2 := rfl
  rw [hgh] at hmid
  set h := n / 2 with hhdef
  have hodd' : n % 2 = 1 := by rw [← Nat.and_one_is_mod]; exact hodd
  have hn2 : n = h + (1 + h) := by omega
  have hh15 : h ≤ 15 := by omega
  have hW : W < 256 ^ (h + (1 + h)) := by rw [← hn2, ← two_pow_eight_mul]; exact hWlt
  set F := W % 256 ^ h with hFdef
  set S := W / 256 ^ (h + 1) with hSdef
  have hF : F < 256 ^ h := Nat.mod_lt _ (by positivity)
  have hS : S < 256 ^ h := by
    rw [hSdef, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    calc W < 256 ^ (h + (1 + h)) := hW
      _ = 256 ^ (h + (h + 1)) := by ring_nf
  have hmid' : W / 256 ^ h % 256 = 0 := by rw [← wLet_eq]; exact hmid
  have hdec : W = F + (0 + S * 256 ^ 1) * 256 ^ h := by
    have h1 := Nat.mod_add_div W (256 ^ h)
    have h2 := Nat.mod_add_div (W / 256 ^ h) 256
    have h3 : W / 256 ^ h / 256 = S := by
      rw [hSdef, Nat.div_div_eq_div_mul, pow_succ]
    rw [hmid', h3] at h2
    rw [pow_one]
    calc W = F + 256 ^ h * (W / 256 ^ h) := h1.symm
      _ = F + (0 + S * 256) * 256 ^ h := by rw [← h2]; ring
  have hI : Co2K.sigInv GW k = 4 * h + F <<< 12 := by
    unfold Co2K.sigInv
    rw [sliceEnt_eq, hgh, pow_zero, Nat.div_one]
  have hSg : Co2K.sigma GW k = 4 * h + S <<< 12 := by
    unfold Co2K.sigma
    have hS' : wWord (GW k) / 256 ^ (Nat.succ h) < 256 ^ h := hS
    rw [sliceEnt_eq, hgh, Nat.mod_eq_of_lt hS']
  have hh' : h < 1024 := by omega
  have hletF : ∀ i < h, wLet F i < 254 := by
    intro i hi
    have := hl i (by omega)
    rw [wLet_eq] at this ⊢
    rw [hdec, byte_add_high hi] at this
    omega
  have hletS : ∀ i < h, wLet S i < 254 := by
    intro i hi
    have := hl (h + 1 + i) (by omega)
    rw [wLet_eq] at this ⊢
    rw [hSdef, Nat.div_div_eq_div_mul, ← pow_add]
    omega
  have hIok : entOK (Co2K.sigInv GW k) 254 15 = true := by
    rw [hI, entOK_iff, wLen_mk _ _ hh', wWord_mk _ _ hh', two_pow_eight_mul]
    exact ⟨hF, hh15, hletF⟩
  have hSok : entOK (Co2K.sigma GW k) 254 15 = true := by
    rw [hSg, entOK_iff, wLen_mk _ _ hh', wWord_mk _ _ hh', two_pow_eight_mul]
    exact ⟨hS, hh15, hletS⟩
  have hinvS : bval gen (wWord (Co2K.sigInv GW k)) (wLen (Co2K.sigInv GW k)) =
      (bval gen (wWord (Co2K.sigma GW k)) (wLen (Co2K.sigma GW k)))⁻¹ := by
    rw [hsig, (invEnt_spec gen hIok (by norm_num)).2.2, inv_inv]
  refine ⟨hSok, hIok, hinvS, ?_⟩
  rw [← hinvS, hI, hSg, wLen_mk _ _ hh', wWord_mk _ _ hh', wLen_mk _ _ hh', wWord_mk _ _ hh',
    hn2, hdec, bval_concat gen hF, bval_concat gen (by norm_num : (0 : ℕ) < 256 ^ 1),
    bval_one gen (by norm_num : (0 : ℕ) < 256)]
  simp [letV, mul_assoc]

theorem gwOK_spec {GW : ℕ → ℕ} (h : gwOK GW = true) :
    ∀ k, 1 ≤ k → k ≤ 5 → gwShape GW k = true := by
  have e : gwOK GW = andB (andB (andB (andB (andB true (gwShape GW 1)) (gwShape GW 2))
      (gwShape GW 3)) (gwShape GW 4)) (gwShape GW 5) := rfl
  rw [e] at h
  simp only [andB_eq, Bool.and_eq_true, Bool.true_and] at h
  intro k h1 h5
  interval_cases k <;> simp_all

theorem letInvAB_spec {G : Type*} [Group G] (gen : ℕ → G) {GW : ℕ → ℕ}
    (hGW : ∀ k, 1 ≤ k → k ≤ 5 → gwShape GW k = true) {x : ℕ} (hx : x < 10) :
    entOK (Co2K.letInvAB GW x) 254 31 = true ∧
      bval gen (wWord (Co2K.letInvAB GW x)) (wLen (Co2K.letInvAB GW x)) =
        (letV (fun k => bval gen (wWord (GW (k + 1))) (wLen (GW (k + 1)))) x)⁻¹ := by
  have hs : Nat.shiftRight x 1 = x / 2 := by
    change x >>> 1 = x / 2
    rw [Nat.shiftRight_eq_div_pow, pow_one]
  have hm : Nat.land x 1 = x % 2 := Nat.and_one_is_mod x
  have e : Co2K.letInvAB GW x = Bool.rec (motive := fun _ => ℕ) (GW (x / 2 + 1))
      (invEnt (GW (x / 2 + 1))) (Nat.beq (x % 2) 0) := by
    unfold Co2K.letInvAB
    rw [hs, hm]
  have hg := hGW (x / 2 + 1) (by omega) (by omega)
  unfold gwShape at hg
  simp only [andB_eq, Bool.and_eq_true] at hg
  have hent : entOK (GW (x / 2 + 1)) 254 31 = true := entOK_mono hg.1 (by norm_num) le_rfl
  rw [e]
  have h255 : x ≠ 255 := by omega
  rcases Nat.mod_two_eq_zero_or_one x with h2 | h2
  · rw [h2]
    change entOK (invEnt (GW (x / 2 + 1))) 254 31 = true ∧
      bval gen (wWord (invEnt (GW (x / 2 + 1)))) (wLen (invEnt (GW (x / 2 + 1)))) = _
    obtain ⟨i1, -, i3⟩ := invEnt_spec gen hent (by norm_num)
    refine ⟨i1, ?_⟩
    rw [i3]
    simp [letV, h255, h2]
  · rw [h2]
    change entOK (GW (x / 2 + 1)) 254 31 = true ∧
      bval gen (wWord (GW (x / 2 + 1))) (wLen (GW (x / 2 + 1))) = _
    refine ⟨hent, ?_⟩
    simp [letV, h255, h2]

theorem piInv_spec {G : Type*} [Group G] (gen : ℕ → G) {GW : ℕ → ℕ}
    (hGW : ∀ k, 1 ≤ k → k ≤ 5 → gwShape GW k = true) {w : ℕ} (hw : entOK w 10 16 = true) :
    entOK (Co2K.piInv GW w) 254 496 = true ∧
      bval gen (wWord (Co2K.piInv GW w)) (wLen (Co2K.piInv GW w)) =
        (bval (fun k => bval gen (wWord (GW (k + 1))) (wLen (GW (k + 1)))) (wWord w) (wLen w))⁻¹ := by
  set gen' := fun k => bval gen (wWord (GW (k + 1))) (wLen (GW (k + 1)))
  obtain ⟨-, hn, hl⟩ := (entOK_iff _ _ _).1 hw
  set n := wLen w
  set W := wWord w
  set P : ℕ → ℕ := fun k => Nat.rec (motive := fun _ => ℕ) 0
    (fun k acc => CFSG.KC.Loop.strictN acc (fun a =>
      Co2K.catEnt a (Co2K.letInvAB GW (CFSG.KC.HOrb.byte W (Nat.sub (Nat.sub n 1) k))))) k
    with hPdef
  have hp : Co2K.piInv GW w = P n := rfl
  have key : ∀ k ≤ n, entOK (P k) 254 (31 * k) = true ∧ bval gen (wWord (P k)) (wLen (P k)) =
      ((List.range k).map fun t => (letV gen' (wLet W (n - 1 - t)))⁻¹).prod := by
    intro k
    induction k with
    | zero =>
      intro _
      have h0 : wLen 0 = 0 := by decide
      refine ⟨entOK_zero 254, ?_⟩
      change bval gen (wWord 0) (wLen 0) = _
      rw [h0, bval_zero]
      rfl
    | succ k ih =>
      intro hk
      obtain ⟨h1, h2⟩ := ih (by omega)
      have e : P (k + 1) = Co2K.catEnt (P k)
          (Co2K.letInvAB GW (CFSG.KC.HOrb.byte W (n - 1 - k))) := by
        change CFSG.KC.Loop.strictN (P k) _ = _
        rw [strictN_eq]
        rfl
      have hx : CFSG.KC.HOrb.byte W (n - 1 - k) < 10 := hl _ (by omega)
      obtain ⟨l1, l2⟩ := letInvAB_spec gen hGW hx
      obtain ⟨c1, -, c3⟩ := catEnt_spec gen h1 l1 (by omega)
      rw [e, c3, h2, l2, List.range_succ, List.map_append, List.prod_append]
      exact ⟨by rw [Nat.mul_succ]; exact c1, by simp; rfl⟩
  obtain ⟨k1, k2⟩ := key n le_rfl
  refine ⟨by rw [hp]; exact entOK_mono k1 le_rfl (by omega), ?_⟩
  rw [hp, k2, bval, List.prod_inv_reverse, List.map_map]
  rw [← map_range_rev ((fun x => x⁻¹) ∘ fun i => letV gen' (wLet W i)) n]
  rfl

theorem hWord_spec {G : Type*} [Group G] (gen : ℕ → G) (H : Subgroup G)
    (hsub : ∀ j, entOK (CFSG.KC.Co2B.sub j) (nat_lit 4) (nat_lit 16) = true ∧
      bval gen (wWord (CFSG.KC.Co2B.sub j)) (wLen (CFSG.KC.Co2B.sub j)) ∈ H) (hl : ℕ) :
    ∀ k ≤ 32, entOK (Co2K.hWord hl k) 254 (16 * k) = true ∧
      bval gen (wWord (Co2K.hWord hl k)) (wLen (Co2K.hWord hl k)) ∈ H := by
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : wLen 0 = 0 := by decide
    refine ⟨entOK_zero 254, ?_⟩
    change bval gen (wWord 0) (wLen 0) ∈ H
    rw [h0, bval_zero]
    exact H.one_mem
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2⟩ := ih (by omega)
    set x := CFSG.KC.HOrb.byte hl k
    set q := Bool.rec (motive := fun _ => ℕ) (invEnt (CFSG.KC.Co2B.sub (Nat.shiftRight x 1)))
      (CFSG.KC.Co2B.sub (Nat.shiftRight x 1)) (Nat.beq (Nat.land x 1) 0) with hq
    have e : Co2K.hWord hl (k + 1) = Co2K.catEnt (Co2K.hWord hl k) q := by
      have e0 : Co2K.hWord hl (k + 1) =
          CFSG.KC.Loop.strictN (Co2K.hWord hl k) (fun a => Co2K.catEnt a q) := rfl
      rw [e0, strictN_eq]
    obtain ⟨s1, s2⟩ := hsub (Nat.shiftRight x 1)
    have s1' : entOK (CFSG.KC.Co2B.sub (Nat.shiftRight x 1)) 254 16 = true :=
      entOK_mono s1 (by norm_num) le_rfl
    have hq1 : entOK q 254 16 = true ∧ bval gen (wWord q) (wLen q) ∈ H := by
      rw [hq]
      cases Nat.beq (Nat.land x 1) 0
      · obtain ⟨i1, -, i3⟩ := invEnt_spec gen s1' (by norm_num)
        exact ⟨i1, by rw [i3]; exact H.inv_mem s2⟩
      · exact ⟨s1', s2⟩
    obtain ⟨c1, -, c3⟩ := catEnt_spec gen h1 hq1.1 (by omega)
    rw [e, c3]
    exact ⟨by rw [Nat.mul_succ]; exact c1, H.mul_mem h2 hq1.2⟩

theorem rootExp_le (ρ : ℕ) : Co2K.rootExp ρ ≤ 4 := by
  unfold Co2K.rootExp
  cases Nat.beq ρ 1 <;> cases Nat.beq ρ 2 <;> decide

theorem pair_group {G : Type*} [Group G] (H : Subgroup G) {a u v U h k : G} {m : ℕ}
    (ha : a * a = 1) (hcent : ∀ x ∈ H, x * a = a * x) (hk : k ∈ H) (hh : h ∈ H)
    (hP : v * u⁻¹ = k * U * h) (hU : (a⁻¹ * U⁻¹ * a * U) ^ m = 1) :
    (u⁻¹ * a * u * v⁻¹ * a * v) ^ m = 1 := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hka : k⁻¹ * a * k = a := by
    calc k⁻¹ * a * k = k⁻¹ * (a * k) := by group
      _ = k⁻¹ * (k * a) := by rw [hcent k hk]
      _ = a := by group
  have hah : a * h⁻¹ = h⁻¹ * a := by
    calc a * h⁻¹ = h⁻¹ * (h * a) * h⁻¹ := by group
      _ = h⁻¹ * (a * h) * h⁻¹ := by rw [hcent h hh]
      _ = h⁻¹ * a := by group
  have hv : v = k * U * h * u := by
    calc v = v * u⁻¹ * u := by group
      _ = k * U * h * u := by rw [hP]
  have e : u⁻¹ * a * u * v⁻¹ * a * v =
      (h * u)⁻¹ * (a⁻¹ * U⁻¹ * a * U) * ((h * u)⁻¹)⁻¹ := by
    rw [hv]
    calc u⁻¹ * a * u * (k * U * h * u)⁻¹ * a * (k * U * h * u)
        = u⁻¹ * (a * h⁻¹) * U⁻¹ * (k⁻¹ * a * k) * U * h * u := by group
      _ = u⁻¹ * (h⁻¹ * a) * U⁻¹ * a * U * h * u := by rw [hka, hah]
      _ = (h * u)⁻¹ * (a⁻¹ * U⁻¹ * a * U) * ((h * u)⁻¹)⁻¹ := by rw [ha']; group
  rw [e, conj_pow, hU, mul_one, mul_inv_cancel]

theorem pairOK_sound {G : Type*} [Group G] (gen : ℕ → G) (H : Subgroup G) (rep : ℕ → G)
    {blk : ℕ → ℕ} {nf : ℕ} (hrep : rep 0 = 1)
    (hwalk : ∀ w x R y, x < 2 ^ 20 → walkTo blk nf w x R y = true →
      rep x * bval gen (wWord w) (wLen w) * (rep y)⁻¹ ∈ H)
    (hsub : ∀ j, entOK (CFSG.KC.Co2B.sub j) (nat_lit 4) (nat_lit 16) = true ∧
      bval gen (wWord (CFSG.KC.Co2B.sub j)) (wLen (CFSG.KC.Co2B.sub j)) ∈ H)
    (hcent : ∀ x ∈ H, x * gen 0 = gen 0 * x) (ha : gen 0 * gen 0 = 1)
    {GW : ℕ → ℕ} (hGW : gwOK GW = true) {U1 U2 U3 U4 : ℕ}
    (hU : ∀ ρ, 1 ≤ ρ → ρ ≤ 4 → entOK (rootWord U1 U2 U3 U4 ρ) (nat_lit 4) (nat_lit 64) = true ∧
      ((gen 0)⁻¹ * (bval gen (wWord (rootWord U1 U2 U3 U4 ρ)) (wLen (rootWord U1 U2 U3 U4 ρ)))⁻¹ *
        gen 0 * bval gen (wWord (rootWord U1 U2 U3 U4 ρ)) (wLen (rootWord U1 U2 U3 U4 ρ))) ^
          rootExp ρ = 1)
    {XRk i j m w R1 c ρ hl hn R2 : ℕ} (hargs : pairArgsOK i j w hn = true)
    (h : pairOK blk GW nf U1 U2 U3 U4 XRk i j m w R1 c ρ hl hn R2 = true) :
    bval (fun k => bval gen (wWord (GW (k + 1))) (wLen (GW (k + 1)))) (wWord XRk) (wLen XRk) = 1 := by
  set gen' : ℕ → G := fun k => bval gen (wWord (GW (k + 1))) (wLen (GW (k + 1))) with hgen'
  have hGW' := gwOK_spec hGW
  simp only [pairArgsOK, andB_eq, Bool.and_eq_true, Nat.ble_eq] at hargs
  obtain ⟨hi1, hi5, hj1, hj5, hw, hhn⟩ := hargs
  have hw254 : entOK w 254 16 = true := entOK_mono hw (by norm_num) le_rfl
  unfold pairOK at h
  simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨hX, hw1, hcase⟩ := h
  obtain ⟨si1, si2, si3, si4⟩ := gw_spec gen (hGW' i hi1 hi5)
  obtain ⟨sj1, -, -, sj4⟩ := gw_spec gen (hGW' j hj1 hj5)
  set a := gen 0
  set σi := bval gen (wWord (Co2K.sigma GW i)) (wLen (Co2K.sigma GW i))
  set σj := bval gen (wWord (Co2K.sigma GW j)) (wLen (Co2K.sigma GW j))
  set πw := bval gen' (wWord w) (wLen w)
  obtain ⟨p1, p2⟩ := piInv_spec gen hGW' hw
  obtain ⟨c1, -, c3⟩ := catEnt_spec gen p1 si2 (by norm_num)
  obtain ⟨-, -, d3⟩ := catEnt_spec gen sj1 c1 (by norm_num)
  have hPv : bval gen (wWord (Co2K.pairWord GW i j w)) (wLen (Co2K.pairWord GW i j w)) =
      σj * (πw⁻¹ * σi⁻¹) := by
    unfold Co2K.pairWord
    rw [d3, c3, p2, si3]
  have hwk1 := hwalk _ 0 R1 c (by norm_num) hw1
  rw [bval_withSent, hPv, hrep, one_mul] at hwk1
  have hlet : ∀ t, 1 ≤ t → t ≤ 5 →
      letV gen' (2 * (t - 1)) = bval gen (wWord (GW t)) (wLen (GW t)) := by
    intro t h1 h5
    have e1 : 2 * (t - 1) ≠ 255 := by omega
    have e2 : 2 * (t - 1) % 2 = 0 := by omega
    have e3 : 2 * (t - 1) / 2 + 1 = t := by omega
    simp only [letV, e1, e2, ite_false, ite_true]
    change bval gen (wWord (GW (2 * (t - 1) / 2 + 1))) (wLen (GW (2 * (t - 1) / 2 + 1))) = _
    rw [e3]
  obtain ⟨ej1, -, ej3⟩ := letEnt_spec gen' (c := 2 * (j - 1)) (by omega)
  obtain ⟨ewj1, -, ewj3⟩ := catEnt_spec gen' hw254 ej1 (by norm_num)
  obtain ⟨ei1, -, ei3⟩ := letEnt_spec gen' (c := 2 * (i - 1)) (by omega)
  obtain ⟨eiwj1, -, eiwj3⟩ := catEnt_spec gen' ei1 ewj1 (by norm_num)
  obtain ⟨ev1, -, ev3⟩ := invEnt_spec gen' hw254 (by norm_num)
  obtain ⟨ea1, -, ea3⟩ := catEnt_spec gen' ev1 eiwj1 (by norm_num)
  obtain ⟨eW, eL, -⟩ := (entOK_iff _ _ _).1 ea1
  have hcase' : (m = Co2K.rootExp ρ ∧ ρ ≤ 4 ∧ walkTo blk nf (withSent (Co2K.catEnt
      (Co2K.rootWord U1 U2 U3 U4 ρ) (Co2K.hWord hl hn))) 0 R2 c = true ∧ 1 ≤ ρ) ∨
      (c = 0 ∧ m = 1) := by
    cases hρ : Nat.beq ρ 0 <;> rw [hρ] at hcase <;> dsimp only at hcase <;>
      simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hcase
    · refine Or.inl ⟨hcase.1, hcase.2.1, hcase.2.2, ?_⟩
      rcases Nat.eq_zero_or_pos ρ with h0 | h0
      · rw [h0] at hρ
        exact absurd hρ (by decide)
      · exact h0
    · exact Or.inr hcase
  have hm4 : m ≤ 4 := by
    rcases hcase' with ⟨hm, -⟩ | ⟨-, hm⟩
    · exact hm ▸ rootExp_le ρ
    · omega
  have hXv : bval gen' (wWord XRk) (wLen XRk) =
      (πw⁻¹ * ((σi⁻¹ * a * σi) * (πw * (σj⁻¹ * a * σj)))) ^ m := by
    have hX' : Co2K.xrelOf i j m w = powEnt (Co2K.catEnt (invEnt w) (Co2K.catEnt
        (Co2K.letEnt (2 * (i - 1))) (Co2K.catEnt w (Co2K.letEnt (2 * (j - 1)))))) m := rfl
    rw [← hX, hX', bval_powEnt gen' eW
      (lt_of_le_of_lt (Nat.mul_le_mul hm4 eL) (by norm_num)), ea3, ev3, eiwj3, ei3, ewj3, ej3, hlet i hi1 hi5,
      hlet j hj1 hj5, si4, sj4]
  rw [hXv]
  have hre : πw⁻¹ * ((σi⁻¹ * a * σi) * (πw * (σj⁻¹ * a * σj))) =
      (σi * πw)⁻¹ * a * (σi * πw) * σj⁻¹ * a * σj := by group
  have hvu : σj * (πw⁻¹ * σi⁻¹) = σj * (σi * πw)⁻¹ := by group
  rw [hre]
  rw [hvu] at hwk1
  rcases hcase' with ⟨hm, hρ4, hw2, hρ1⟩ | ⟨hc0, hm1⟩
  ·
    obtain ⟨u1, u2⟩ := hU ρ hρ1 hρ4
    obtain ⟨hh1, hh2⟩ := hWord_spec gen H hsub hl hn hhn
    obtain ⟨-, -, f3⟩ := catEnt_spec gen (entOK_mono u1 (by norm_num) le_rfl)
      (entOK_mono hh1 le_rfl (n' := 512) (by omega)) (by norm_num)
    have hwk2 := hwalk _ 0 R2 c (by norm_num) hw2
    rw [bval_withSent, f3, hrep, one_mul] at hwk2
    rw [hm]
    refine pair_group H ha hcent (H.mul_mem hwk1 (H.inv_mem hwk2)) hh2 ?_ u2
    group
  ·
    rw [hc0, hrep, inv_one, mul_one] at hwk1
    rw [hm1]
    refine pair_group H ha hcent (U := 1) hwk1 H.one_mem ?_ (by group)
    group

private theorem dec7_ONE7 : dec7 ONE7 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.one_apply] <;> decide

private theorem wf7_ONE7 : wf7 ONE7 = true := by quickRfl

private theorem lX_labOne : Nat.beq (lX labOne) ONE7 = true := by quickRfl

private theorem lXI_labOne : Nat.beq (lXI labOne) ONE7 = true := by quickRfl

private noncomputable def jList (WT : ℕ → ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, J => J :: jList WT k (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight J (nat_lit 1))
      (Nat.shiftRight J (jLen J (WT (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)))

private noncomputable def wOf (WT : ℕ → ℕ) (J : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (nat_lit 0)
    (WT (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)))
    (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1))

private noncomputable def jAll (WT : ℕ → ℕ) (Cs : List ℕ) : List ℕ :=
  Cs.flatMap fun C => jList WT (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8))

private theorem chunkRec_eq (blk WT : ℕ → ℕ) (INV nC L : ℕ) : ∀ k J S,
    LceP.chunkRec blk WT INV nC L k J S =
      (jList WT k J).foldl (fun S J => factStep blk INV nC L J S (fct blk (sI S)) (wOf WT J)) S
  | 0, _, _ => rfl
  | k + 1, J, S => by
    change Bool.rec (motive := fun _ => ℕ)
      (LceP.chunkRec blk WT INV nC L k (Nat.shiftRight J (nat_lit 1))
        (factStep blk INV nC L J S (fct blk (sI S)) (nat_lit 0)))
      (CFSG.KC.Loop.strictN (CFSG.KC.Loop.strictN (Nat.land (Nat.shiftRight J (nat_lit 1))
        (nat_lit 65535)) WT)
        (fun w => LceP.chunkRec blk WT INV nC L k (Nat.shiftRight J (jLen J w))
          (factStep blk INV nC L J S (fct blk (sI S)) w)))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)) = _
    simp only [jList, List.foldl_cons, wOf, LceP.strictN_eq]
    cases Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1) <;> exact chunkRec_eq blk WT INV nC L k _ _

private theorem runFacts_eq (blk WT : ℕ → ℕ) (INV nC L : ℕ) : ∀ Cs S,
    runFacts blk WT INV nC L Cs S =
      (jAll WT Cs).foldl (fun S J => factStep blk INV nC L J S (fct blk (sI S)) (wOf WT J)) S
  | [], _ => rfl
  | C :: Cs, S => by
    change CFSG.KC.Loop.strictN (LceP.chunkRec blk WT INV nC L (Nat.land C (nat_lit 255))
      (Nat.shiftRight C (nat_lit 8)) S) (runFacts blk WT INV nC L Cs) = _
    rw [LceP.strictN_eq, runFacts_eq blk WT INV nC L Cs, chunkRec_eq]
    simp only [jAll, List.flatMap_cons, List.foldl_append]

private noncomputable def labRec (WT LB LETs : ℕ → ℕ) (Hs : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => Bool.rec (motive := fun _ => Nat)
      (CFSG.KC.Loop.strictN (labStep LB LETs Hs J S (nat_lit 0)) (ih (Nat.shiftRight J (nat_lit 1))))
      (CFSG.KC.Loop.strictN (CFSG.KC.Loop.strictN (Nat.land (Nat.shiftRight J (nat_lit 1))
        (nat_lit 65535)) WT) (fun w =>
        CFSG.KC.Loop.strictN (labStep LB LETs Hs J S w) (ih (Nat.shiftRight J (jLen J w)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1))) k

private theorem labRec_eq (WT LB LETs : ℕ → ℕ) (Hs : ℕ) : ∀ k J S,
    labRec WT LB LETs Hs k J S =
      (jList WT k J).foldl (fun S J => labStep LB LETs Hs J S (wOf WT J)) S
  | 0, _, _ => rfl
  | k + 1, J, S => by
    change Bool.rec (motive := fun _ => ℕ)
      (CFSG.KC.Loop.strictN (labStep LB LETs Hs J S (nat_lit 0))
        (labRec WT LB LETs Hs k (Nat.shiftRight J (nat_lit 1))))
      (CFSG.KC.Loop.strictN (CFSG.KC.Loop.strictN (Nat.land (Nat.shiftRight J (nat_lit 1))
        (nat_lit 65535)) WT)
        (fun w => CFSG.KC.Loop.strictN (labStep LB LETs Hs J S w)
          (labRec WT LB LETs Hs k (Nat.shiftRight J (jLen J w)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)) = _
    simp only [jList, List.foldl_cons, wOf, LceP.strictN_eq]
    cases Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1) <;> exact labRec_eq WT LB LETs Hs k _ _

private theorem runLab_eq (WT LB LETs : ℕ → ℕ) (Hs : ℕ) : ∀ Cs S,
    runLab WT LB LETs Hs Cs S = (jAll WT Cs).foldl (fun S J => labStep LB LETs Hs J S (wOf WT J)) S
  | [], _ => rfl
  | C :: Cs, S => by
    change CFSG.KC.Loop.strictN (labRec WT LB LETs Hs (Nat.land C (nat_lit 255))
      (Nat.shiftRight C (nat_lit 8)) S) (runLab WT LB LETs Hs Cs) = _
    rw [LceP.strictN_eq, runLab_eq WT LB LETs Hs Cs, labRec_eq]
    simp only [jAll, List.flatMap_cons, List.foldl_append]

private noncomputable def idsF (m I J : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) I
    (Bool.rec (motive := fun _ => ℕ) (nat_lit 0) I
      (Nat.blt (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) m))
    (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1))

private noncomputable def idsRec (WT : ℕ → ℕ) (m : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => Bool.rec (motive := fun _ => Nat)
      (ih (Nat.shiftRight J (nat_lit 1)) S)
      (CFSG.KC.Loop.strictN (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) (fun id =>
        CFSG.KC.Loop.strictN (WT id) (fun w =>
          ih (Nat.shiftRight J (jLen J w))
            (Bool.rec (motive := fun _ => Nat) (nat_lit 0) S (Nat.blt id m)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1))) k

private theorem idsRec_eq (WT : ℕ → ℕ) (m : ℕ) : ∀ k J S,
    idsRec WT m k J S = (jList WT k J).foldl (idsF m) S
  | 0, _, _ => rfl
  | k + 1, J, S => by
    change Bool.rec (motive := fun _ => ℕ) (idsRec WT m k (Nat.shiftRight J (nat_lit 1)) S)
      (CFSG.KC.Loop.strictN (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) (fun id =>
        CFSG.KC.Loop.strictN (WT id) (fun w => idsRec WT m k (Nat.shiftRight J (jLen J w))
          (Bool.rec (motive := fun _ => ℕ) (nat_lit 0) S (Nat.blt id m)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)) = _
    simp only [jList, List.foldl_cons, idsF, LceP.strictN_eq]
    cases Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1) <;> exact idsRec_eq WT m k _ _

private theorem runIds_eq (WT : ℕ → ℕ) (m : ℕ) : ∀ Cs S,
    CFSG.KC.LceSR.runIds WT m Cs S = (jAll WT Cs).foldl (idsF m) S
  | [], _ => rfl
  | C :: Cs, S => by
    change CFSG.KC.Loop.strictN (idsRec WT m (Nat.land C (nat_lit 255))
      (Nat.shiftRight C (nat_lit 8)) S) (CFSG.KC.LceSR.runIds WT m Cs) = _
    rw [LceP.strictN_eq, runIds_eq WT m Cs, idsRec_eq]
    simp only [jAll, List.flatMap_cons, List.foldl_append]

section Lab

variable {G X : Type*} [Group G] [Group X] (gen : ℕ → G) (π : X →* G)
  (ψ : X →* (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ)

private noncomputable def LabWF (L : ℕ) : Prop := wf7 (lX L) = true ∧ wf7 (lXI L) = true

private noncomputable def LabHolds (rep : ℕ → G) (R L : ℕ) : Prop :=
  ∃ l : X, π l = LceP.el gen rep R ∧
    ((ψ l : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ) : Matrix (Fin 10) (Fin 10) (ZMod 7)) = dec7 (lX L) ∧
    ((ψ l⁻¹ : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ) : Matrix (Fin 10) (Fin 10) (ZMod 7)) =
      dec7 (lXI L)

private noncomputable def LRefs (blk LB : ℕ → ℕ) (INV nC : ℕ) (rep : ℕ → G) (i : ℕ) : Prop :=
  ∀ h < i, recOK INV nC (fct blk h) = true ∧ LabWF (LB h) ∧ LabHolds gen π ψ rep (fct blk h) (LB h)

private noncomputable def WL (rep : ℕ → G) (s W ft : ℕ) (u : G) (M : Matrix (Fin 10) (Fin 10) (ZMod 7))
    (p st acc : ℕ) : Prop :=
  st / 1048576 = 0 ∨ ∃ cur < 1048576, st = cur + 1048576 * (W / 256 ^ p) ∧ wf7 acc = true ∧
    ((p ≤ ft ∧ ∃ a : X, π a = rep s * LceP.bv gen W p * (rep cur)⁻¹ ∧
        ((ψ a : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ) : Matrix (Fin 10) (Fin 10) (ZMod 7)) =
          dec7 acc) ∨
      (ft < p ∧ ∃ a b : X, π a * u * π b = rep s * LceP.bv gen W p * (rep cur)⁻¹ ∧
        ((ψ a : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ) : Matrix (Fin 10) (Fin 10) (ZMod 7)) * M *
          ((ψ b : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ) : Matrix (Fin 10) (Fin 10) (ZMod 7)) =
          dec7 acc))

private theorem WL_start (rep : ℕ → G) {s : ℕ} (W ft : ℕ) (u : G) (M : Matrix (Fin 10) (Fin 10) (ZMod 7))
    (hs : s < 1048576) : WL gen π ψ rep s W ft u M 0 (wStart s W) ONE7 := by
  right
  refine ⟨s, hs, ?_, wf7_ONE7, Or.inl ⟨Nat.zero_le _, 1, ?_, ?_⟩⟩
  · unfold wStart
    rw [LceP.lor20 _ hs, pow_zero, Nat.div_one]
    ring
  · rw [map_one, LceP.bv_zero, mul_one, mul_inv_cancel]
  · rw [map_one, Units.val_one, dec7_ONE7]

private theorem WL_ext {rep : ℕ → G} {s W ft : ℕ} {u : G} {M : Matrix (Fin 10) (Fin 10) (ZMod 7)}
    {p acc cur cur' B : ℕ} {c : X} (hp : p ≠ ft) (hacc : wf7 acc = true) (hB : wf7 B = true)
    (hX : (p ≤ ft ∧ ∃ a : X, π a = rep s * LceP.bv gen W p * (rep cur)⁻¹ ∧
        ((ψ a : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ) : Matrix (Fin 10) (Fin 10) (ZMod 7)) =
          dec7 acc) ∨
      (ft < p ∧ ∃ a b : X, π a * u * π b = rep s * LceP.bv gen W p * (rep cur)⁻¹ ∧
        ((ψ a : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ) : Matrix (Fin 10) (Fin 10) (ZMod 7)) * M *
          ((ψ b : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ) : Matrix (Fin 10) (Fin 10) (ZMod 7)) =
          dec7 acc))
    (hc : π c = rep cur * LceP.lv gen (wLet W p) * (rep cur')⁻¹)
    (hcB : ((ψ c : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ) : Matrix (Fin 10) (Fin 10) (ZMod 7)) =
      dec7 B) :
    wf7 (mul7 acc B) = true ∧
    ((p + 1 ≤ ft ∧ ∃ a : X, π a = rep s * LceP.bv gen W (p + 1) * (rep cur')⁻¹ ∧
        ((ψ a : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ) : Matrix (Fin 10) (Fin 10) (ZMod 7)) =
          dec7 (mul7 acc B)) ∨
      (ft < p + 1 ∧ ∃ a b : X, π a * u * π b = rep s * LceP.bv gen W (p + 1) * (rep cur')⁻¹ ∧
        ((ψ a : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ) : Matrix (Fin 10) (Fin 10) (ZMod 7)) * M *
          ((ψ b : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ) : Matrix (Fin 10) (Fin 10) (ZMod 7)) =
          dec7 (mul7 acc B))) := by
  obtain ⟨hw, hd⟩ := mul7_sound hacc hB
  have e : rep s * LceP.bv gen W (p + 1) * (rep cur')⁻¹ =
      (rep s * LceP.bv gen W p * (rep cur)⁻¹) * (rep cur * LceP.lv gen (wLet W p) * (rep cur')⁻¹) := by
    rw [LceP.bv_succ]
    group
  refine ⟨hw, ?_⟩
  rcases hX with ⟨hp', a, ha, haψ⟩ | ⟨hp', a, b, hab, habψ⟩
  · refine Or.inl ⟨by omega, a * c, ?_, ?_⟩
    · rw [map_mul, ha, hc, e]
    · rw [map_mul, Units.val_mul, haψ, hcB, hd]
  · refine Or.inr ⟨by omega, a, b * c, ?_, ?_⟩
    · rw [map_mul, e, ← hab, hc]
      group
    · rw [map_mul, Units.val_mul, hd, ← habψ, hcB]
      simp only [mul_assoc]

private theorem sF_cases (R st : ℕ) :
    sF R st = 0 ∨ (st % 268435456 = fxc R ∧ sF R st = fy R + st / 268435456 * 1048576) := by
  rw [LceP.sF_eq]
  split_ifs with h
  · exact Or.inr ⟨h, rfl⟩
  · exact Or.inl rfl

private theorem sB_cases (R st : ℕ) :
    sB R st = 0 ∨ (st % 268435456 = fyic R ∧ sB R st = fx R + st / 268435456 * 1048576) := by
  rw [LceP.sB_eq]
  split_ifs with h
  · exact Or.inr ⟨h, rfl⟩
  · exact Or.inl rfl

private theorem fwd_arith {R st cur W p : ℕ} (hcur : cur < 1048576)
    (hst : st = cur + 1048576 * (W / 256 ^ p)) (hm : st % 268435456 = fxc R) :
    cur = fx R ∧ wLet W p = fc R ∧
      fy R + st / 268435456 * 1048576 = fy R + 1048576 * (W / 256 ^ (p + 1)) := by
  rw [LceP.fxc_eq] at hm
  have hfx := LceP.fx_lt R
  have hfc := LceP.fc_lt R
  have h3 : st / 268435456 = W / 256 ^ (p + 1) := by
    rw [← LceP.div256_succ]
    omega
  refine ⟨by omega, ?_, by rw [h3]; ring⟩
  rw [LceP.wLet_eq]
  omega

private theorem bwd_arith {R st cur W p : ℕ} (hcur : cur < 1048576)
    (hst : st = cur + 1048576 * (W / 256 ^ p)) (hm : st % 268435456 = fyic R)
    (hic : fic R < 256) :
    cur = fy R ∧ wLet W p = fic R ∧
      fx R + st / 268435456 * 1048576 = fx R + 1048576 * (W / 256 ^ (p + 1)) := by
  rw [LceP.fyic_eq] at hm
  have hfy := LceP.fy_lt R
  have h3 : st / 268435456 = W / 256 ^ (p + 1) := by
    rw [← LceP.div256_succ]
    omega
  refine ⟨by omega, ?_, by rw [h3]; ring⟩
  rw [LceP.wLet_eq]
  omega

private theorem WL_ref {blk LB : ℕ → ℕ} {INV INV8 L nC i : ℕ} (hinv : invOK INV INV8 L = true)
    {rep : ℕ → G} {s W ft : ℕ} {u : G} {M : Matrix (Fin 10) (Fin 10) (ZMod 7)} {p st acc : ℕ}
    (e : ℕ) (hrefs : LRefs gen π ψ blk LB INV nC rep i) (hp : p ≠ ft)
    (hI : WL gen π ψ rep s W ft u M p st acc) :
    WL gen π ψ rep s W ft u M (p + 1) (refStep blk i e st)
      (pushL (LB (Nat.shiftRight e (nat_lit 1))) (Nat.land e (nat_lit 1)) acc) := by
  unfold refStep pushL
  rw [LceP.brec_eq]
  split_ifs with hh
  · rw [Nat.blt_eq] at hh
    simp only [LceP.strictN_eq]
    obtain ⟨hrec, ⟨hwX, hwXI⟩, l, hl, hlX, hlXI⟩ := hrefs _ hh
    set R := fct blk (Nat.shiftRight e (nat_lit 1))
    have hlv := (LceP.lv_fic gen blk hinv hrec).1
    rw [LceP.brec_eq, LceP.brec_eq]
    split_ifs with hd
    ·
      rcases hI with hdead | ⟨cur, hcur, hst, hacc, hX⟩
      · left
        rcases sB_cases R st with h0 | ⟨hm, h1⟩
        · rw [h0]
        · rw [h1]
          have := LceP.fx_lt R
          omega
      · rcases sB_cases R st with h0 | ⟨hm, h1⟩
        · left
          rw [h0]
        · right
          obtain ⟨hc, hw, hs⟩ := bwd_arith hcur hst hm (LceP.fic_lt blk _)
          refine ⟨fx R, LceP.fx_lt R, by rw [h1, hs], ?_⟩
          refine WL_ext gen π ψ hp hacc hwXI hX (c := l⁻¹) ?_ hlXI
          have hlv' : LceP.lv gen (fic R) = (LceP.lv gen (fc R))⁻¹ := hlv
          rw [map_inv, hl, hw, hlv', hc]
          unfold LceP.el
          group
    ·
      rcases hI with hdead | ⟨cur, hcur, hst, hacc, hX⟩
      · left
        rcases sF_cases R st with h0 | ⟨hm, h1⟩
        · rw [h0]
        · rw [h1]
          have := LceP.fy_lt R
          omega
      · rcases sF_cases R st with h0 | ⟨hm, h1⟩
        · left
          rw [h0]
        · right
          obtain ⟨hc, hw, hs⟩ := fwd_arith hcur hst hm
          refine ⟨fy R, LceP.fy_lt R, by rw [h1, hs], ?_⟩
          refine WL_ext gen π ψ hp hacc hwX hX (c := l) ?_ hlX
          rw [hl, hw, hc]
          rfl
  · left
    rfl

private theorem WL_own {rep : ℕ → G} {s W ft Ri Li p st acc : ℕ} (hp : p = ft)
    (hLi : wf7 (lX Li) = true)
    (hI : WL gen π ψ rep s W ft (LceP.el gen rep Ri) (dec7 (lX Li)) p st acc) :
    WL gen π ψ rep s W ft (LceP.el gen rep Ri) (dec7 (lX Li)) (p + 1) (sF Ri st)
      (pushL Li (nat_lit 0) acc) := by
  have hpush : pushL Li (nat_lit 0) acc = mul7 acc (lX Li) := rfl
  rw [hpush]
  rcases hI with hdead | ⟨cur, hcur, hst, hacc, hX⟩
  · left
    rcases sF_cases Ri st with h0 | ⟨hm, h1⟩
    · rw [h0]
    · rw [h1]
      have := LceP.fy_lt Ri
      omega
  · rcases sF_cases Ri st with h0 | ⟨hm, h1⟩
    · left
      rw [h0]
    · right
      obtain ⟨hc, hw, hs⟩ := fwd_arith hcur hst hm
      obtain ⟨hw7, hd⟩ := mul7_sound hacc hLi
      refine ⟨fy Ri, LceP.fy_lt Ri, by rw [h1, hs], hw7, Or.inr ⟨by omega, ?_⟩⟩
      rcases hX with ⟨-, a, ha, haψ⟩ | ⟨hlt, -⟩
      · refine ⟨a, 1, ?_, ?_⟩
        · rw [map_one, mul_one, ha, LceP.bv_succ, hw, hc]
          unfold LceP.el
          group
        · rw [map_one, Units.val_one, mul_one, haψ, hd]
      · omega

private theorem walk_lab {blk LB : ℕ → ℕ} {INV INV8 L nC i : ℕ} (hinv : invOK INV INV8 L = true)
    {rep : ℕ → G} {s W Ri Li ft n : ℕ} (hrefs : LRefs gen π ψ blk LB INV nC rep i)
    (hLi : wf7 (lX Li) = true) :
    ∀ k ≤ n, ∀ J st acc,
      WL gen π ψ rep s W ft (LceP.el gen rep Ri) (dec7 (lX Li)) (n - k) st acc →
      WL gen π ψ rep s W ft (LceP.el gen rep Ri) (dec7 (lX Li)) n
        (walkGo blk i Ri ft n k J st) (labGo LB Li ft n k J acc)
  | 0, _, J, st, acc, hI => by
    rw [Nat.sub_zero] at hI
    exact hI
  | k + 1, hk, J, st, acc, hI => by
    change WL gen π ψ rep s W ft (LceP.el gen rep Ri) (dec7 (lX Li)) n
      (Bool.rec (motive := fun _ => ℕ)
        (walkGo blk i Ri ft n k (Nat.shiftRight J 32) (refStep blk i (Nat.land J 4294967295) st))
        (walkGo blk i Ri ft n k J (sF Ri st)) (Nat.beq (Nat.sub n (Nat.succ k)) ft))
      (Bool.rec (motive := fun _ => ℕ)
        ((fun e => CFSG.KC.Loop.strictN (pushL (LB (Nat.shiftRight e 1)) (Nat.land e 1) acc)
            (labGo LB Li ft n k (Nat.shiftRight J 32))) (Nat.land J 4294967295))
        (CFSG.KC.Loop.strictN (pushL Li 0 acc) (labGo LB Li ft n k J))
        (Nat.beq (Nat.sub n (Nat.succ k)) ft))
    have e : n - k = n - (k + 1) + 1 := by omega
    cases hb : Nat.beq (Nat.sub n (Nat.succ k)) ft
    · dsimp only
      rw [LceP.strictN_eq]
      apply walk_lab hinv hrefs hLi k (by omega)
      rw [e]
      have hp : n - (k + 1) ≠ ft := by
        intro h
        have h2 : Nat.beq (Nat.sub n (Nat.succ k)) ft = true := by
          rw [Nat.beq_eq]
          exact h
        rw [hb] at h2
        exact Bool.false_ne_true h2
      exact WL_ref gen π ψ hinv _ hrefs hp hI
    · dsimp only
      rw [LceP.strictN_eq]
      apply walk_lab hinv hrefs hLi k (by omega)
      rw [e]
      exact WL_own gen π ψ (Nat.eq_of_beq_eq_true hb) hLi hI

private theorem walk_cyc {blk LB : ℕ → ℕ} {INV INV8 L nC i : ℕ} (hinv : invOK INV INV8 L = true)
    {rep : ℕ → G} {s W n : ℕ} {u : G} {M : Matrix (Fin 10) (Fin 10) (ZMod 7)}
    (hrefs : LRefs gen π ψ blk LB INV nC rep i) :
    ∀ k ≤ n, ∀ J st acc, WL gen π ψ rep s W n u M (n - k) st acc →
      WL gen π ψ rep s W n u M n (cycWalk blk i k J st) (cycLab LB k J acc)
  | 0, _, J, st, acc, hI => by
    rw [Nat.sub_zero] at hI
    exact hI
  | k + 1, hk, J, st, acc, hI => by
    change WL gen π ψ rep s W n u M n
      (CFSG.KC.Loop.strictN (refStep blk i (Nat.land J 4294967295) st)
        (cycWalk blk i k (Nat.shiftRight J 32)))
      ((fun e => CFSG.KC.Loop.strictN (pushL (LB (Nat.shiftRight e 1)) (Nat.land e 1) acc)
        (cycLab LB k (Nat.shiftRight J 32))) (Nat.land J 4294967295))
    dsimp only
    rw [LceP.strictN_eq, LceP.strictN_eq]
    apply walk_cyc hinv hrefs k (by omega)
    rw [show n - k = n - (k + 1) + 1 by omega]
    exact WL_ref gen π ψ hinv _ hrefs (by omega) hI

private noncomputable def LInv (blk LB : ℕ → ℕ) (INV nC i N : ℕ) : Prop :=
  ∃ rep : ℕ → G, rep 0 = 1 ∧ ∀ rep' : ℕ → G, (∀ k < N, rep' k = rep k) →
    LRefs gen π ψ blk LB INV nC rep' i

private noncomputable def LGood (blk LB : ℕ → ℕ) (INV nC S T I : ℕ) : Prop :=
  S = 0 ∨ T = 0 ∨ I = 0 ∨ 4294967296 < T ∨
    (1 ≤ sN S ∧ T = sI S + 1 ∧ LInv gen π ψ blk LB INV nC (sI S) (sN S))

private theorem unit_mid {A B C : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ}
    {M : Matrix (Fin 10) (Fin 10) (ZMod 7)}
    (h : (A : Matrix (Fin 10) (Fin 10) (ZMod 7)) * M * B = C) :
    ((A⁻¹ * C * B⁻¹ : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ) : Matrix (Fin 10) (Fin 10) (ZMod 7)) =
      M := by
  rw [Units.val_mul, Units.val_mul, ← h]
  simp only [mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, mul_one]

private theorem lab_of_walk {u : G} {M Q : Matrix (Fin 10) (Fin 10) (ZMod 7)} {a b t : X}
    (hab : π a * u * π b = π t)
    (hψ : ((ψ a : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ) : Matrix (Fin 10) (Fin 10) (ZMod 7)) * M *
      ((ψ b : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ) : Matrix (Fin 10) (Fin 10) (ZMod 7)) =
      ((ψ t : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ) : Matrix (Fin 10) (Fin 10) (ZMod 7)))
    (hMQ : M * Q = 1) :
    ∃ l : X, π l = u ∧
      ((ψ l : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ) : Matrix (Fin 10) (Fin 10) (ZMod 7)) = M ∧
      ((ψ l⁻¹ : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ) : Matrix (Fin 10) (Fin 10) (ZMod 7)) = Q := by
  have hM : ((ψ (a⁻¹ * t * b⁻¹) : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ) :
      Matrix (Fin 10) (Fin 10) (ZMod 7)) = M := by
    rw [map_mul, map_mul, map_inv, map_inv]
    exact unit_mid hψ
  refine ⟨a⁻¹ * t * b⁻¹, ?_, hM, ?_⟩
  · rw [map_mul, map_mul, map_inv, map_inv, ← hab]
    group
  · rw [map_inv]
    calc (((ψ (a⁻¹ * t * b⁻¹))⁻¹ : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ) :
          Matrix (Fin 10) (Fin 10) (ZMod 7))
        = (((ψ (a⁻¹ * t * b⁻¹))⁻¹ : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ) :
          Matrix (Fin 10) (Fin 10) (ZMod 7)) * (M * Q) := by rw [hMQ, mul_one]
      _ = Q := by rw [← hM, ← mul_assoc, Units.inv_mul, one_mul]

private theorem labStep_cases (LB LETs : ℕ → ℕ) (Hs J T w : ℕ) :
    labStep LB LETs Hs J T w = 0 ∨ labStep LB LETs Hs J T w = T + 1 := by
  unfold labStep
  cases Nat.blt (nat_lit 0) T
  · exact Or.inl rfl
  · dsimp only
    cases Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1) <;> dsimp only
    · cases Nat.beq (LB (Nat.sub T (nat_lit 1))) labOne
      · exact Or.inl rfl
      · exact Or.inr rfl
    · cases labWalk LB LETs (Nat.sub T (nat_lit 1)) J w
        (hint Hs (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)))
      · exact Or.inl rfl
      · exact Or.inr rfl

private theorem LGood_step {blk WT ST LB LETs : ℕ → ℕ} {INV INV8 L nC m Hs K : ℕ}
    (hinv : invOK INV INV8 L = true)
    (hW2 : ∀ id < m, wKind (WT id) = 2 → LceP.bv gen (wWord (WT id)) (wLen (WT id)) = 1)
    (hW3 : ∀ id < m, wKind (WT id) = 3 → hint Hs id < K ∧
      LceP.bv gen (wWord (WT id)) (wLen (WT id)) =
        LceP.bv gen (wWord (ST (hint Hs id))) (wLen (ST (hint Hs id))))
    (hLET : ∀ j < K, ∃ t : X,
      π t = LceP.bv gen (wWord (ST j)) (wLen (ST j)) ∧ ((ψ t : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ) :
        Matrix (Fin 10) (Fin 10) (ZMod 7)) = dec7 (lX (LETs j)))
    {S T I : ℕ} (J : ℕ) (hG : LGood gen π ψ blk LB INV nC S T I) :
    LGood gen π ψ blk LB INV nC (factStep blk INV nC L J S (fct blk (sI S)) (wOf WT J))
      (labStep LB LETs Hs J T (wOf WT J)) (idsF m I J) := by
  rcases hG with h0 | h0 | h0 | h0 | ⟨hN, hT, rep, hrep0, hrefs⟩
  · left
    rw [h0]
    rfl
  · right; left
    rw [h0]
    rfl
  · right; right; left
    rw [h0]
    unfold idsF
    cases Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1) <;>
      cases Nat.blt (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) m <;> rfl
  · rcases labStep_cases LB LETs Hs J T (wOf WT J) with h | h
    · right; left
      exact h
    · right; right; right; left
      rw [h]
      omega
  set i := sI S with hidef
  set N := sN S with hNdef
  have hi32 : i < 4294967296 := LceP.sI_lt S
  have hS0 : Nat.blt (nat_lit 0) S = true := by
    rw [Nat.blt_eq]
    change 0 < S
    have : S / 4294967296 ≥ 1 := by rw [← LceP.sN_eq]; exact hN
    omega
  have hT0 : Nat.blt (nat_lit 0) T = true := by
    rw [Nat.blt_eq]
    change 0 < T
    omega
  have hT1 : Nat.sub T (nat_lit 1) = i := by
    change T - 1 = i
    omega
  have hnext : ∀ N' : ℕ, 1 ≤ N' → LInv gen π ψ blk LB INV nC (i + 1) N' → ∀ I' : ℕ,
      LGood gen π ψ blk LB INV nC (mkS (Nat.succ i) N') (T + 1) I' := by
    intro N' hN' hL I'
    rcases Nat.lt_or_ge (i + 1) 4294967296 with hlt | hge
    · right; right; right; right
      have e1 : sI (mkS (Nat.succ i) N') = i + 1 := by
        rw [LceP.sI_eq, LceP.mkS_eq N' hlt]
        omega
      have e2 : sN (mkS (Nat.succ i) N') = N' := by
        rw [LceP.sN_eq, LceP.mkS_eq N' hlt]
        omega
      rw [e1, e2]
      exact ⟨hN', by omega, hL⟩
    · right; right; right; left
      omega
  unfold factStep labStep idsF wOf
  rw [hS0, hT0, hT1]
  dsimp only
  cases hJ : Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)
  ·
    dsimp only
    cases hft : fTree INV nC L (fct blk i) N
    · left
      rfl
    cases hlb : Nat.beq (LB i) labOne
    · right; left
      rfl
    dsimp only
    refine hnext (N + 1) (by omega) ?_ _
    unfold fTree at hft
    simp only [LceP.andB_iff, Nat.beq_eq, Nat.blt_eq] at hft
    obtain ⟨hrR, hfy, hfx, -⟩ := hft
    have hLB : LB i = labOne := Nat.eq_of_beq_eq_true hlb
    have hX1 : lX (LB i) = ONE7 := by rw [hLB]; exact Nat.eq_of_beq_eq_true lX_labOne
    have hX2 : lXI (LB i) = ONE7 := by rw [hLB]; exact Nat.eq_of_beq_eq_true lXI_labOne
    set R := fct blk i
    refine ⟨Function.update rep N (rep (fx R) * LceP.lv gen (fc R)), ?_, fun rep' hag h hh => ?_⟩
    · rw [Function.update_of_ne (show (0 : ℕ) ≠ N by omega)]
      exact hrep0
    have hag' : ∀ k < N, rep' k = rep k := by
      intro k hk
      rw [hag k (by omega), Function.update_of_ne (show k ≠ N by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | rfl
    · exact hrefs rep' hag' h hh
    · refine ⟨hrR, ⟨by rw [hX1]; exact wf7_ONE7, by rw [hX2]; exact wf7_ONE7⟩, 1, ?_, ?_, ?_⟩
      · rw [map_one]
        unfold LceP.el
        rw [hfy, hag N (by omega), Function.update_self, hag' _ hfx, mul_inv_cancel]
      · rw [map_one, Units.val_one, hX1, dec7_ONE7]
      · rw [inv_one, map_one, Units.val_one, hX2, dec7_ONE7]
  ·
    dsimp only
    set id := Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535) with hiddef
    cases hid : Nat.blt id m
    · right; right; left
      rfl
    have hidm : id < m := LceP.blt_true hid
    set w := WT id
    set fs := Nat.land (Nat.shiftRight J (nat_lit 17)) (nat_lit 1048575)
    set ft := Nat.land (Nat.shiftRight J (nat_lit 37)) (nat_lit 65535)
    cases hwk : walkOK blk INV nC i (fct blk i) w fs ft J
    · left
      rfl
    cases hlw : labWalk LB LETs i J w (hint Hs id)
    · right; left
      rfl
    dsimp only
    set R := fct blk i
    refine hnext N hN ⟨rep, hrep0, fun rep' hag h hh => ?_⟩ _
    rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | rfl
    · exact hrefs rep' hag h hh
    unfold walkOK at hwk
    simp only [LceP.andB_iff, LceP.orB_iff, Nat.blt_eq, Nat.beq_eq, Nat.add_eq] at hwk
    obtain ⟨hrec, hft, hkind, hwalk⟩ := hwk
    unfold labWalk at hlw
    rw [LceP.letB_eq] at hlw
    simp only [LceP.andB_iff, Nat.beq_eq] at hlw
    obtain ⟨⟨hwX, hwXI⟩, hmul, hlab⟩ := hlw
    have hfs : fs < 1048576 := by
      change Nat.land (Nat.shiftRight J 17) 1048575 < 1048576
      rw [LceP.land20]
      omega
    have hrefs' := hrefs rep' hag
    have hstart := WL_start gen π ψ rep' (wWord w) ft (LceP.el gen rep' R) (dec7 (lX (LB i))) hfs
    have hW := walk_lab gen π ψ hinv hrefs' hwX (wLen w) le_rfl (Nat.shiftRight J 53) _ _
      (by rw [Nat.sub_self]; exact hstart)
    rw [hwalk, hlab] at hW
    obtain ⟨-, hd⟩ := mul7_sound hwX hwXI
    have hMQ : dec7 (lX (LB i)) * dec7 (lXI (LB i)) = 1 := by
      rw [← hd, hmul, dec7_ONE7]
    refine ⟨hrec, ⟨hwX, hwXI⟩, ?_⟩
    rcases hW with hdead | ⟨cur, hcur, hst, -, hX⟩
    · exfalso
      omega
    have hW1 : wWord w / 256 ^ wLen w = 1 := by omega
    have hc : cur = fs := by omega
    rcases hX with ⟨hle, -⟩ | ⟨-, a, b, hab, habψ⟩
    · exfalso
      omega
    rw [hc] at hab
    rcases hkind with hk2 | ⟨hk3, hfs0⟩
    ·
      have hbv := hW2 id hidm hk2
      have htg : target LETs w (hint Hs id) = ONE7 := by
        unfold target
        rw [show Nat.beq (wKind w) (nat_lit 3) = false by rw [hk2]; rfl]
      rw [htg, dec7_ONE7] at habψ
      refine lab_of_walk π ψ (a := a) (b := b) (t := 1) ?_ ?_ hMQ
      · rw [hab, hbv, mul_one, mul_inv_cancel, map_one]
      · rw [habψ, map_one, Units.val_one]
    ·
      obtain ⟨hK, hbv⟩ := hW3 id hidm hk3
      obtain ⟨t, ht, htψ⟩ := hLET _ hK
      have htg : target LETs w (hint Hs id) = lX (LETs (hint Hs id)) := by
        unfold target
        rw [show Nat.beq (wKind w) (nat_lit 3) = true by rw [hk3]; rfl]
      rw [htg, ← htψ] at habψ
      have h0 : rep' 0 = 1 := by rw [hag 0 (by omega), hrep0]
      refine lab_of_walk π ψ (a := a) (b := b) ?_ habψ hMQ
      rw [hab, hfs0, h0, one_mul, inv_one, mul_one, hbv, ht]

end Lab

theorem lab_sound {G X : Type*} [Group G] [Group X] (gen : ℕ → G) (π : X →* G)
    (ψ : X →* (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ)
    {blk WT RT ST LB LETs : ℕ → ℕ} {INV INV8 L nC nf m Hs K S0 S1 T0 T1 : ℕ} {Cs : List ℕ}
    (h : coneOk blk WT RT ST LB LETs INV INV8 L nC nf m Hs K S0 S1 T0 T1 Cs = true)
    (hRT : ∀ r, wWord (RT r) < 2 ^ (8 * wLen (RT r)) ∧ bval gen (wWord (RT r)) (wLen (RT r)) = 1)
    (hLET : ∀ j < K, wf7 (lX (LETs j)) = true ∧ ∃ t : X,
      π t = bval gen (wWord (ST j)) (wLen (ST j)) ∧ ((ψ t : Matrix (Fin 10) (Fin 10) (ZMod 7)) =
        dec7 (lX (LETs j))))
    {nf' c wid R V : ℕ} (hnf : nf' = nf) (hc : c < 2 ^ 20) (hcyc : cycOK blk WT LB nf' c wid R V = true)
    (hwid : wid < m := by decide) :
    ∃ ν : X, π ν = 1 ∧ ((ψ ν : Matrix (Fin 10) (Fin 10) (ZMod 7)) = dec7 V) := by
  subst nf'
  unfold coneOk at h
  obtain ⟨hwords, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hinv, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨-, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hnf, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hS0, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hS1, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hT0, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hT1, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hhints, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hids, h⟩ := (LceP.andB_iff _ _).1 h
  obtain ⟨hrun, hlab⟩ := (LceP.andB_iff _ _).1 h
  have hnf' : nf < 4294967296 := LceP.blt_true hnf
  have hw : ∀ j < m, (wKind (WT j) = 2 → LceP.bv gen (wWord (WT j)) (wLen (WT j)) = 1) ∧
      (wKind (WT j) = 3 → hint Hs j < K ∧ LceP.bv gen (wWord (WT j)) (wLen (WT j)) =
        LceP.bv gen (wWord (ST (hint Hs j))) (wLen (ST (hint Hs j)))) := by
    intro j hj
    have hl := LceP.hintLoop (fun j H => (fun w r => Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) true
          (wSub INV (wWord w) (wLen w) (wWord (ST r)) (wLen (ST r))) (Nat.beq (wKind w) (nat_lit 3)))
        (wRel INV INV8 (wWord w) (wLen w) (wWord (RT r)) (wLen (RT r)))
        (Nat.beq (wKind w) (nat_lit 2))) (WT j) (Nat.land H (nat_lit 65535)))
      m (nat_lit 16) m le_rfl Hs hwords j hj
    rw [Nat.sub_self, Nat.zero_add] at hl
    obtain ⟨hw2, hw3⟩ := LceP.word_check hl
    have hlt := (LceP.allRec_iff (fun k => Bool.rec (motive := fun _ => Bool) true
      (Nat.blt (hint Hs k) K) (Nat.beq (wKind (WT k)) (nat_lit 3))) m).1 hhints j hj
    refine ⟨fun hk => LceP.wRel_sound gen hinv (hw2 hk) (hRT _).1 (hRT _).2, fun hk => ⟨?_, ?_⟩⟩
    · have hb : Nat.beq (wKind (WT j)) (nat_lit 3) = true := by rw [hk]; rfl
      rw [hb] at hlt
      exact LceP.blt_true hlt
    · exact LceP.wSub_sound gen (hw3 hk)
  have hstep := fun (J : ℕ) {S T I : ℕ} => LGood_step gen π ψ (blk := blk) (WT := WT) (ST := ST)
    (LB := LB) (LETs := LETs) (L := L) (nC := nC) (m := m) (Hs := Hs) (K := K) (S := S) (T := T)
    (I := I) hinv (fun id hid => (hw id hid).1) (fun id hid => (hw id hid).2)
    (fun j hj => (hLET j hj).2) J
  have hfold : ∀ (l : List ℕ) (S T I : ℕ), LGood gen π ψ blk LB INV nC S T I →
      LGood gen π ψ blk LB INV nC
        (l.foldl (fun S J => factStep blk INV nC L J S (fct blk (sI S)) (wOf WT J)) S)
        (l.foldl (fun S J => labStep LB LETs Hs J S (wOf WT J)) T) (l.foldl (idsF m) I) := by
    intro l
    induction l with
    | nil => intro S T I hG; exact hG
    | cons J l ih =>
      intro S T I hG
      simp only [List.foldl_cons]
      exact ih _ _ _ (hstep J hG)
  have hS0' : S0 = mkS 0 1 := Nat.eq_of_beq_eq_true hS0
  have hT0' : T0 = 1 := Nat.eq_of_beq_eq_true hT0
  have hG0 : LGood gen π ψ blk LB INV nC S0 T0 1 := by
    right; right; right; right
    have e1 : sI S0 = 0 := by rw [hS0', LceP.sI_eq, LceP.mkS_eq 1 (by norm_num)]
    have e2 : sN S0 = 1 := by rw [hS0', LceP.sN_eq, LceP.mkS_eq 1 (by norm_num)]
    rw [e1, e2, hT0']
    exact ⟨le_rfl, rfl, fun _ => 1, rfl, fun _ _ h hh => absurd hh (Nat.not_lt_zero h)⟩
  have hG1 := hfold (jAll WT Cs) S0 T0 1 hG0
  rw [← runFacts_eq, ← runLab_eq, ← runIds_eq, Nat.eq_of_beq_eq_true hrun,
    Nat.eq_of_beq_eq_true hlab, Nat.eq_of_beq_eq_true hids, Nat.eq_of_beq_eq_true hS1,
    Nat.eq_of_beq_eq_true hT1] at hG1
  have hL : ∃ rep : ℕ → G, LRefs gen π ψ blk LB INV nC rep nf := by
    rcases hG1 with h0 | h0 | h0 | h0 | ⟨-, -, rep, -, hrefs⟩
    · rw [LceP.mkS_eq nC hnf'] at h0
      have h0' : nf = 0 := by omega
      exact ⟨fun _ => 1, fun h hh => absurd hh (by omega)⟩
    · exact absurd h0 (Nat.succ_ne_zero nf)
    · exact absurd h0 one_ne_zero
    · exfalso
      change 4294967296 < nf + 1 at h0
      omega
    · have e1 : sI (mkS nf nC) = nf := by
        rw [LceP.sI_eq, LceP.mkS_eq nC hnf']
        omega
      rw [e1] at hrefs
      exact ⟨rep, hrefs rep fun _ _ => rfl⟩
  obtain ⟨rep, hrefs⟩ := hL
  unfold cycOK at hcyc
  rw [LceP.letB_eq] at hcyc
  simp only [LceP.andB_iff, Nat.beq_eq, Nat.add_eq] at hcyc
  obtain ⟨hk2, hwalk, hlab'⟩ := hcyc
  have hc' : c < 1048576 := by simpa using hc
  have hstart := WL_start gen π ψ rep (wWord (WT wid)) (wLen (WT wid)) 1 1 hc'
  have hW := walk_cyc gen π ψ hinv hrefs (wLen (WT wid)) le_rfl R _ _
    (by rw [Nat.sub_self]; exact hstart)
  rw [hwalk, hlab'] at hW
  rcases hW with hdead | ⟨cur, hcur, hst, -, hX⟩
  · exfalso
    omega
  have hc0 : cur = c := by omega
  rcases hX with ⟨-, a, ha, haψ⟩ | ⟨hlt, -⟩
  · refine ⟨a, ?_, haψ⟩
    rw [ha, hc0, (hw wid hwid).1 hk2, mul_one, mul_inv_cancel]
  · exact absurd hlt (lt_irrefl _)

end CFSG.Certificates.Co2Kill

end
