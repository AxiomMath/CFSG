module

public import Certificates.Data.Kernel.E7Plane.Check
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.E7Plane

open Finset

theorem letB_eq (y : ℕ) (k : ℕ → Bool) : letB y k = k y := by
  cases y <;> rfl

theorem letN_eq (y : ℕ) (k : ℕ → ℕ) : letN y k = k y := by
  cases y <;> rfl

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by
  cases a <;> rfl

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by
  cases a <;> rfl

theorem notB_eq (a : Bool) : notB a = !a := by
  cases a <;> rfl

theorem toN_eq (b : Bool) : toN b = if b = true then 1 else 0 := by
  cases b <;> rfl

theorem allN_succ (n : ℕ) (f : ℕ → Bool) : allN (n + 1) f = andB (f n) (allN n f) := rfl

theorem allN_eq_true {n : ℕ} {f : ℕ → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    rw [allN_succ, andB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem lenL_eq {α : Type} (L : List α) : lenL L = L.length := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    change Nat.succ (lenL L) = _
    rw [ih, List.length_cons]

theorem fld_eq (X w i : ℕ) : fld X w i = X / 2 ^ (w * i) % 2 ^ w := by
  change (X >>> (w * i)) &&& (1 <<< w - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem f7_eq (X i : ℕ) : f7 X i = X / 2 ^ (7 * i) % 2 ^ 7 := by
  change (X >>> (7 * i)) &&& (2 ^ 7 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem ln_eq (V i : ℕ) : ln V i = V / 2 ^ (8 * i) % 2 ^ 8 := by
  change (V >>> (8 * i)) &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem fld_lt (X w i : ℕ) : fld X w i < 2 ^ w := by
  rw [fld_eq]
  exact Nat.mod_lt _ (by positivity)

theorem f7_lt (X i : ℕ) : f7 X i < 2 ^ 7 := by
  rw [f7_eq]
  exact Nat.mod_lt _ (by positivity)

theorem land_mask (X w : ℕ) : Nat.land X (Nat.sub (Nat.shiftLeft 1 w) 1) = X % 2 ^ w := by
  change X &&& (1 <<< w - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]

theorem div_mod_add_mul {A B k M : ℕ} (hA : A < k) : (A + B * k) / k % M = B % M := by
  rw [Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hA, zero_add]

theorem div_mod_add_mul_high {A B k M : ℕ} (hk : 0 < k) :
    (A + B * (M * k)) / k % M = A / k % M := by
  rw [← mul_assoc, Nat.add_mul_div_right _ _ hk, Nat.add_mul_mod_self_right]

theorem mod_pow_div_mod {X m k w : ℕ} (h : k + w ≤ m) :
    X % 2 ^ m / 2 ^ k % 2 ^ w = X / 2 ^ k % 2 ^ w := by
  conv_rhs => rw [← Nat.mod_add_div X (2 ^ m)]
  have e : 2 ^ m * (X / 2 ^ m) = X / 2 ^ m * 2 ^ (m - k - w) * (2 ^ w * 2 ^ k) := by
    rw [mul_comm (2 ^ m), mul_assoc, ← pow_add, ← pow_add]
    congr 2
    omega
  rw [e, div_mod_add_mul_high (by positivity)]

theorem orN_succ (n w : ℕ) (f : ℕ → ℕ) :
    orN (n + 1) w f = Nat.lor (orN n w f) (Nat.shiftLeft (f n) (Nat.mul w n)) := rfl

theorem orN_spec {n w : ℕ} {f : ℕ → ℕ} (hf : ∀ i < n, f i < 2 ^ w) :
    orN n w f = ∑ i ∈ range n, f i * 2 ^ (w * i) ∧ orN n w f < 2 ^ (w * n) := by
  induction n with
  | zero => exact ⟨rfl, by simp [orN]⟩
  | succ n ih =>
    obtain ⟨e, hlt⟩ := ih fun i hi => hf i (Nat.lt_succ_of_lt hi)
    have hfn := hf n (Nat.lt_succ_self n)
    have e' : orN (n + 1) w f = orN n w f + f n * 2 ^ (w * n) := by
      rw [orN_succ]
      change orN n w f ||| f n <<< (w * n) = _
      rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hlt, Nat.shiftLeft_eq, add_comm]
    rw [e', sum_range_succ, ← e]
    refine ⟨rfl, ?_⟩
    have : f n * 2 ^ (w * n) + 2 ^ (w * n) ≤ 2 ^ (w * (n + 1)) := by
      rw [mul_add, mul_one, pow_add, ← Nat.succ_mul, mul_comm (2 ^ (w * n))]
      exact Nat.mul_le_mul_right _ hfn
    omega

theorem sum_digit {n w : ℕ} {f : ℕ → ℕ} (hf : ∀ i < n, f i < 2 ^ w) {i : ℕ} (hi : i < n) :
    (∑ j ∈ range n, f j * 2 ^ (w * j)) / 2 ^ (w * i) % 2 ^ w = f i := by
  induction n with
  | zero => exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    have hf' : ∀ j < n, f j < 2 ^ w := fun j hj => hf j (Nat.lt_succ_of_lt hj)
    rw [sum_range_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · have e : 2 ^ (w * n) = 2 ^ (w * (n - i - 1)) * (2 ^ w * 2 ^ (w * i)) := by
        rw [← pow_add, ← pow_add]
        congr 1
        obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 + i := ⟨n - i - 1, by omega⟩
        rw [show d + 1 + i - i - 1 = d by omega]
        ring
      rw [e, ← mul_assoc, div_mod_add_mul_high (by positivity), ih hf' hi]
    · rw [div_mod_add_mul ((orN_spec hf').1 ▸ (orN_spec hf').2), Nat.mod_eq_of_lt (hf i hi)]

theorem orN_digit {n w : ℕ} {f : ℕ → ℕ} (hf : ∀ i < n, f i < 2 ^ w) {i : ℕ} (hi : i < n) :
    orN n w f / 2 ^ (w * i) % 2 ^ w = f i := by
  rw [(orN_spec hf).1]
  exact sum_digit hf hi

theorem packL_cons {α : Type} (w : ℕ) (f : α → ℕ) (x : α) (L : List α) :
    packL w f (x :: L) = Nat.lor (f x) (Nat.shiftLeft (packL w f L) w) := rfl

theorem packL_digit {α : Type} {w : ℕ} {f : α → ℕ} :
    ∀ (L : List α), (∀ x ∈ L, f x < 2 ^ w) → ∀ l (hl : l < L.length),
      packL w f L / 2 ^ (w * l) % 2 ^ w = f (L[l]'hl)
  | [], _, l, hl => absurd hl (Nat.not_lt_zero l)
  | x :: L, hL, l, hl => by
    have hx := hL x List.mem_cons_self
    have e : packL w f (x :: L) = f x + packL w f L * 2 ^ w := by
      rw [packL_cons]
      change f x ||| packL w f L <<< w = _
      rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq, add_comm]
    rw [e]
    cases l with
    | zero =>
      rw [mul_zero, pow_zero, Nat.div_one, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
      rfl
    | succ l =>
      rw [mul_add, mul_one, pow_add, mul_comm (2 ^ (w * l)), ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hx, zero_add,
        packL_digit L (fun y hy => hL y (List.mem_cons_of_mem x hy)) l]
      rfl

theorem fld_packL {α : Type} {w : ℕ} {f : α → ℕ} {L : List α} (hL : ∀ x ∈ L, f x < 2 ^ w)
    {l : ℕ} (hl : l < L.length) : fld (packL w f L) w l = f (L[l]'hl) := by
  rw [fld_eq, packL_digit L hL l hl]

theorem eq_of_f7 {X Y : ℕ} (hX : X < 2 ^ 49) (hY : Y < 2 ^ 49)
    (h : ∀ j < 7, f7 X j = f7 Y j) : X = Y := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rcases lt_or_ge b 49 with hb | hb
  · have hj := h (b / 7) (by omega)
    rw [f7_eq, f7_eq] at hj
    have := congrArg (fun z => Nat.testBit z (b % 7)) hj
    simp only [Nat.testBit_mod_two_pow,
      Nat.testBit_div_two_pow] at this
    have hb7 : b % 7 < 7 := Nat.mod_lt _ (by omega)
    simp only [hb7, decide_true, Bool.true_and] at this
    rwa [show b % 7 + 7 * (b / 7) = b by omega] at this
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hX (Nat.pow_le_pow_right (by omega) hb)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hY (Nat.pow_le_pow_right (by omega) hb))]

theorem testBit_iff_digit (X i : ℕ) : X.testBit i = true ↔ X / 2 ^ i % 2 = 1 := by
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]

def KqSpec (Q N : ℕ) (g : ℕ → ℕ) : Prop :=
  ∀ b, Q.testBit b = true ↔ ∃ r < 3, ∃ n < N, b = 2187 * r + n ∧ g n % 3 = r

theorem KqSpec.ext {Q N : ℕ} {g g' : ℕ → ℕ} (h : KqSpec Q N g)
    (e : ∀ n < N, g n % 3 = g' n % 3) : KqSpec Q N g' := by
  intro b
  rw [h b]
  constructor
  · rintro ⟨r, hr, n, hn, hb, hg⟩
    exact ⟨r, hr, n, hn, hb, by rw [← e n hn]; exact hg⟩
  · rintro ⟨r, hr, n, hn, hb, hg⟩
    exact ⟨r, hr, n, hn, hb, by rw [e n hn]; exact hg⟩

theorem rot_eq (Q : ℕ) : rot Q = (Q <<< 2187 ||| Q >>> 4374) &&& (2 ^ 6561 - 1) := by
  rw [← Nat.one_shiftLeft]
  rfl

theorem kqSpec_rot {Q N : ℕ} {g : ℕ → ℕ} (hN : N ≤ 2187) (h : KqSpec Q N g) :
    KqSpec (rot Q) N (fun n => g n + 1) := by
  unfold KqSpec at h ⊢
  intro b
  simp only [rot_eq, Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, h]
  constructor
  · rintro ⟨⟨hb0, r, hr, n, hn, hb, hg⟩ | ⟨r, hr, n, hn, hb, hg⟩, hb1⟩
    · exact ⟨r + 1, by omega, n, hn, by omega, by omega⟩
    · exact ⟨0, by omega, n, hn, by omega, by omega⟩
  · rintro ⟨r, hr, n, hn, hb, hg⟩
    refine ⟨?_, by omega⟩
    by_cases h2 : g n % 3 = 2
    · exact Or.inr ⟨2, by omega, n, hn, by omega, h2⟩
    · exact Or.inl ⟨by omega, r - 1, by omega, n, hn, by omega, by omega⟩

theorem kqSpec_rotk {Q N : ℕ} {g : ℕ → ℕ} (hN : N ≤ 2187) (h : KqSpec Q N g) (k : ℕ) :
    KqSpec (rotk Q k) N (fun n => g n + k) := by
  have key : ∀ i, KqSpec (Nat.rec (motive := fun _ => Nat) Q (fun _ ih => rot ih) i) N
      (fun n => g n + i) := by
    intro i
    induction i with
    | zero => exact h.ext (fun n _ => by simp)
    | succ i ih => exact (kqSpec_rot hN ih).ext (fun n _ => by omega)
  exact (key (k % 3)).ext (fun n _ => by omega)

theorem div_mod_split {n0 s : ℕ} (k : ℕ) (h : n0 < s) :
    (n0 + k * s) % s = n0 ∧ (n0 + k * s) / s = k := by
  refine ⟨by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h], ?_⟩
  rw [Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt h, Nat.zero_add]

theorem kstep_eq (Q m s : ℕ) :
    kstep Q m s = Q ||| (rotk Q m <<< s ||| rotk Q (2 * m) <<< (2 * s)) := by
  unfold kstep
  rw [letN_eq, letN_eq]
  rfl

theorem kqSpec_kstep {Q s : ℕ} {g : ℕ → ℕ} (m : ℕ) (hs : s * 3 ≤ 2187) (h : KqSpec Q s g) :
    KqSpec (kstep Q m s) (s * 3) (fun n => g (n % s) + n / s * m) := by
  have h1 := kqSpec_rotk (by omega) h m
  have h2 := kqSpec_rotk (by omega) h (2 * m)
  unfold KqSpec at h h1 h2 ⊢
  intro b
  simp only [kstep_eq, Nat.testBit_or, Nat.testBit_shiftLeft, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq, h, h1, h2]
  constructor
  · rintro (⟨r, hr, n, hn, hb, hg⟩ | ⟨hsb, r, hr, n, hn, hb, hg⟩ | ⟨hsb, r, hr, n, hn, hb, hg⟩)
    · obtain ⟨e1, e2⟩ := div_mod_split 0 hn
      refine ⟨r, hr, n + 0 * s, by omega, by omega, ?_⟩
      rw [e1, e2]
      simpa using hg
    · obtain ⟨e1, e2⟩ := div_mod_split 1 hn
      refine ⟨r, hr, n + 1 * s, by omega, by omega, ?_⟩
      rw [e1, e2]
      simpa using hg
    · obtain ⟨e1, e2⟩ := div_mod_split 2 hn
      refine ⟨r, hr, n + 2 * s, by omega, by omega, ?_⟩
      rw [e1, e2]
      exact hg
  · rintro ⟨r, hr, n, hn, hb, hg⟩
    rcases lt_or_ge n s with hn0 | hn0
    · rw [Nat.mod_eq_of_lt hn0, Nat.div_eq_of_lt hn0] at hg
      exact Or.inl ⟨r, hr, n, hn0, hb, by simpa using hg⟩
    rcases lt_or_ge n (2 * s) with hn1 | hn1
    · obtain ⟨n0, rfl⟩ : ∃ n0, n = n0 + 1 * s := ⟨n - s, by omega⟩
      obtain ⟨e1, e2⟩ := div_mod_split 1 (by omega : n0 < s)
      rw [e1, e2] at hg
      exact Or.inr (Or.inl ⟨by omega, r, hr, n0, by omega, by omega, by simpa using hg⟩)
    · obtain ⟨n0, rfl⟩ : ∃ n0, n = n0 + 2 * s := ⟨n - 2 * s, by omega⟩
      obtain ⟨e1, e2⟩ := div_mod_split 2 (by omega : n0 < s)
      rw [e1, e2] at hg
      exact Or.inr (Or.inr ⟨by omega, r, hr, n0, by omega, by omega, hg⟩)

noncomputable def kqSteps (m : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => kstep (kqSteps m k) (m k) (3 ^ k)

theorem kqSpec_kqSteps (m : ℕ → ℕ) (k : ℕ) (hk : k ≤ 7) :
    KqSpec (kqSteps m k) (3 ^ k) (fun n => ∑ j ∈ range k, (n / 3 ^ j % 3) * m j) := by
  induction k with
  | zero =>
    intro b
    simp only [kqSteps, pow_zero, range_zero, sum_empty, Nat.zero_mod]
    rw [← pow_zero 2, Nat.testBit_two_pow, decide_eq_true_eq]
    constructor
    · rintro rfl
      exact ⟨0, by omega, 0, by omega, by omega, rfl⟩
    · rintro ⟨r, hr, n, hn, hb, rfl⟩
      omega
  | succ k ih =>
    have hp : 3 ^ k * 3 ≤ 2187 := by
      rw [← pow_succ]
      exact (Nat.pow_le_pow_right (by norm_num) hk).trans (by norm_num)
    rw [pow_succ]
    refine (kqSpec_kstep (m k) hp (ih (by omega))).ext (fun n hn => ?_)
    rw [sum_range_succ]
    have hd : n / 3 ^ k < 3 := (Nat.div_lt_iff_lt_mul (by positivity)).2 (by linarith)
    rw [Nat.mod_eq_of_lt hd]
    congr 2
    refine sum_congr rfl (fun j hj => ?_)
    have hj' : j < k := mem_range.1 hj
    have e : 3 ^ k = 3 ^ j * 3 ^ (k - j) := by rw [← pow_add]; congr 1; omega
    rw [e, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self 3 (by omega))]

theorem kq_eq (W : ℕ) : kq W = kqSteps (res W) 7 := by
  unfold kq
  rw [letN_eq]
  rfl

theorem testBit_kq (W b : ℕ) : (kq W).testBit b = true ↔
    ∃ r < 3, ∃ n < 2187, b = 2187 * r + n ∧
      (∑ j ∈ Finset.range 7, (n / 3 ^ j % 3) * res W j) % 3 = r := by
  rw [kq_eq]
  exact kqSpec_kqSteps (res W) 7 le_rfl b

theorem kq_lt (W : ℕ) {N : ℕ} (hN : 6561 ≤ N) : kq W < 2 ^ N := by
  refine Nat.lt_pow_two_of_testBit _ fun b hb => ?_
  cases hh : (kq W).testBit b
  · rfl
  · obtain ⟨r, hr, n, hn, rfl, -⟩ := (testBit_kq W b).1 hh
    omega

end CFSG.KC.E7Plane

end
