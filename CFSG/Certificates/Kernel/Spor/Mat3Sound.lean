module

public import CFSG.Certificates.Kernel.Orders.Mat3
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KS.Mat3

open CFSG.KC.Ord CFSG.KC.Loop

@[expose] def bv (b1 b2 : Bool) : ZMod 3 := if b1 then 1 else if b2 then 2 else 0

@[expose] def mat3 (d N X : Nat) : Matrix (Fin d) (Fin d) (ZMod 3) :=
  fun i j => bv (X.testBit (d * i.val + j.val)) (X.testBit (N + (d * i.val + j.val)))

@[expose] def Canon3 (N X : Nat) : Prop :=
  X < 2 ^ (N + N) ∧ ∀ t, X.testBit t = true → X.testBit (N + t) = false

theorem strictN_eq3 (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem andB_true3 {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem land_eq3 (a b : Nat) : Nat.land a b = a &&& b := rfl
theorem lor_eq3 (a b : Nat) : Nat.lor a b = a ||| b := rfl
theorem xor_eq3 (a b : Nat) : Nat.xor a b = a ^^^ b := rfl
theorem shr_eq3 (a b : Nat) : Nat.shiftRight a b = a >>> b := rfl
theorem shl_eq3 (a b : Nat) : Nat.shiftLeft a b = a <<< b := rfl
theorem add_eq3 (a b : Nat) : Nat.add a b = a + b := rfl
theorem mul_eq3 (a b : Nat) : Nat.mul a b = a * b := rfl

theorem pow_sub_one_eq (n : Nat) : Nat.sub (Nat.shiftLeft 1 n) 1 = 2 ^ n - 1 := by
  change 1 <<< n - 1 = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem testBit_add_disj {a b : Nat} (h : ∀ p, ¬(a.testBit p = true ∧ b.testBit p = true))
    (p : Nat) : (a + b).testBit p = (a.testBit p || b.testBit p) := by
  have h0 : a &&& b = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    have := h i
    cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all
  have hab : a + b < 2 ^ (a + b) := Nat.lt_two_pow_self
  have ha : a < 2 ^ (a + b) := lt_of_le_of_lt (by omega) hab
  have hb : b < 2 ^ (a + b) := lt_of_le_of_lt (by omega) hab
  have hv : BitVec.ofNat (a + b) a &&& BitVec.ofNat (a + b) b = 0#(a + b) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb, h0, BitVec.toNat_zero]
  have key := congrArg BitVec.toNat (BitVec.add_eq_or_of_and_eq_zero _ _ hv)
  rw [BitVec.toNat_add, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hab] at key
  rw [key, Nat.testBit_or]

theorem dm_eq3 {d i j : Nat} (hj : j < d) : (d * i + j) / d = i ∧ (d * i + j) % d = j := by
  have hd : 0 < d := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hj, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]

theorem idx_lt3 {d i j : Nat} (hi : i < d) (hj : j < d) : d * i + j < d * d := by
  have := Nat.mul_le_mul_left d (Nat.succ_le_of_lt hi)
  rw [Nat.mul_succ] at this
  omega

theorem rep1_sum (s m : Nat) :
    (2 ^ s - 1) * ∑ i ∈ Finset.range m, 2 ^ (s * i) + 1 = 2 ^ (s * m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, Nat.add_right_comm, ih, Nat.mul_succ, Nat.pow_add]
    obtain ⟨q, hq⟩ : ∃ q, 2 ^ s = q + 1 :=
      ⟨2 ^ s - 1, by have := Nat.one_le_two_pow (n := s); omega⟩
    rw [hq, Nat.add_sub_cancel]
    ring

theorem rep1_eq3 {s : Nat} (hs : 0 < s) (m : Nat) :
    rep1 s m = ∑ i ∈ Finset.range m, 2 ^ (s * i) := by
  have h2 : 2 ≤ 2 ^ s := by
    have := Nat.pow_le_pow_right (n := 2) (by omega) hs
    simpa using this
  unfold rep1
  change (1 <<< (s * m) - 1) / (1 <<< s - 1) = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.one_mul, ← rep1_sum s m,
    Nat.add_sub_cancel]
  exact Nat.mul_div_cancel_left _ (by omega)

theorem sum_lt3 {s : Nat} (hs : 0 < s) (m : Nat) :
    ∑ i ∈ Finset.range m, 2 ^ (s * i) < 2 ^ (s * m) := by
  have h := rep1_sum s m
  have h2 : 1 ≤ 2 ^ s - 1 := by
    have := Nat.pow_le_pow_right (n := 2) (by omega) hs
    simp at this
    omega
  have := Nat.le_mul_of_pos_left (∑ i ∈ Finset.range m, 2 ^ (s * i)) h2
  omega

theorem rep1_testBit {s : Nat} (hs : 0 < s) (m u : Nat) :
    (rep1 s m).testBit u = true ↔ ∃ c, c < m ∧ u = s * c := by
  rw [rep1_eq3 hs]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.add_comm, ← Nat.mul_one (2 ^ (s * m)),
      Nat.two_pow_add_eq_or_of_lt (sum_lt3 hs m), Nat.testBit_or, Nat.mul_one, Nat.testBit_two_pow,
      Bool.or_eq_true, ih, decide_eq_true_iff]
    constructor
    · rintro (h | ⟨c, hc, rfl⟩)
      · exact ⟨m, by omega, h.symm⟩
      · exact ⟨c, by omega, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
      · exact Or.inr ⟨c, hc, rfl⟩
      · exact Or.inl rfl

theorem consts3_facts {d f N LO RM CI ONE UP : Nat} (hc : consts3OK d f N LO RM CI ONE UP = true) :
    0 < d ∧ N = d * d ∧ LO = 2 ^ N - 1 ∧ RM = 2 ^ d - 1 ∧ CI = rep1 d d ∧
      ONE = rep1 (d + 1) d := by
  unfold consts3OK at hc
  obtain ⟨h1, hc⟩ := andB_true3 hc
  obtain ⟨-, hc⟩ := andB_true3 hc
  obtain ⟨hN, hc⟩ := andB_true3 hc
  obtain ⟨hLO, hc⟩ := andB_true3 hc
  obtain ⟨hRM, hc⟩ := andB_true3 hc
  obtain ⟨hCI, hc⟩ := andB_true3 hc
  obtain ⟨hONE, -⟩ := andB_true3 hc
  refine ⟨Nat.le_of_ble_eq_true h1, Nat.eq_of_beq_eq_true hN, ?_, ?_, Nat.eq_of_beq_eq_true hCI,
    Nat.eq_of_beq_eq_true hONE⟩
  · rw [Nat.eq_of_beq_eq_true hLO, pow_sub_one_eq]
  · rw [Nat.eq_of_beq_eq_true hRM, pow_sub_one_eq]

theorem valid3_iff {N LO X : Nat} (hLO : LO = 2 ^ N - 1) : valid3 N LO X = true ↔ Canon3 N X := by
  subst hLO
  unfold valid3
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := andB_true3 h
    have h1' : X >>> (N + N) = 0 := Nat.eq_of_beq_eq_true h1
    have h2' : X &&& (2 ^ N - 1) &&& X >>> N = 0 := Nat.eq_of_beq_eq_true h2
    refine ⟨?_, fun t ht => ?_⟩
    · rw [Nat.shiftRight_eq_div_pow] at h1'
      rcases Nat.div_eq_zero_iff.1 h1' with h | h
      · exact absurd h (Nat.two_pow_pos _).ne'
      · exact h
    · by_cases htN : t < N
      · have := congrArg (fun x => Nat.testBit x t) h2'
        simp only [Nat.testBit_and, Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_mod_two_pow,
          Nat.testBit_shiftRight, Nat.zero_testBit, htN, decide_true, Bool.true_and, ht] at this
        exact this
      · rw [Nat.shiftRight_eq_div_pow] at h1'
        have hX : X < 2 ^ (N + N) := by
          rcases Nat.div_eq_zero_iff.1 h1' with h | h
          · exact absurd h (Nat.two_pow_pos _).ne'
          · exact h
        exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hX (Nat.pow_le_pow_right (by omega)
          (by omega)))
  · rintro ⟨hX, hd⟩
    have e1 : Nat.shiftRight X (Nat.add N N) = 0 := by
      change X >>> (N + N) = 0
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hX]
    have e2 : Nat.land (Nat.land X (2 ^ N - 1)) (Nat.shiftRight X N) = 0 := by
      change X &&& (2 ^ N - 1) &&& X >>> N = 0
      apply Nat.eq_of_testBit_eq
      intro t
      simp only [Nat.testBit_and, Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_mod_two_pow,
        Nat.testBit_shiftRight, Nat.zero_testBit]
      cases h : X.testBit t
      · simp
      · rw [hd t h]
        simp
    rw [e1, e2]
    rfl

theorem spread_mul3 {d : Nat} (hd : 0 < d) {y : Nat} (hy : y < 2 ^ d) (k : Nat) (hk : k < d) :
    ∀ (b S : Nat), (∀ i, S.testBit i = true → d ∣ i) →
      (S * y).testBit (d * b + k) = (S.testBit (d * b) && y.testBit k) := by
  have hS0 : ∀ S : Nat, (∀ i, S.testBit i = true → d ∣ i) → S % 2 ^ d < 2 := by
    intro S hS
    have := Nat.lt_pow_two_of_testBit (S % 2 ^ d) (n := 1) (fun i hi => by
      rw [Nat.testBit_mod_two_pow]
      by_cases hid : i < d
      · have : ¬ S.testBit i = true := fun h => by
          obtain ⟨q, hq⟩ := hS i h
          rcases q with _ | q
          · omega
          · have : d ≤ i := by rw [hq]; exact Nat.le_mul_of_pos_right _ (by omega)
            omega
        simp [hid, this]
      · simp [hid])
    simpa using this
  intro b
  induction b with
  | zero =>
    intro S hS
    have h0 := hS0 S hS
    have e : S * y = 2 ^ d * (S / 2 ^ d * y) + S % 2 ^ d * y := by
      conv_lhs => rw [← Nat.div_add_mod S (2 ^ d)]
      ring
    have hlt : S % 2 ^ d * y < 2 ^ d := by
      rcases (by omega : S % 2 ^ d = 0 ∨ S % 2 ^ d = 1) with h | h <;> rw [h] <;> omega
    rw [Nat.mul_zero, Nat.zero_add, e, Nat.testBit_two_pow_mul_add _ hlt, ite_eq_left hk]
    have h0' : S.testBit 0 = decide (S % 2 ^ d = 1) := by
      have : S.testBit 0 = (S % 2 ^ d).testBit 0 := by
        rw [Nat.testBit_mod_two_pow]
        simp [hd]
      rw [this]
      rcases (by omega : S % 2 ^ d = 0 ∨ S % 2 ^ d = 1) with h | h <;> rw [h] <;> rfl
    rw [h0']
    rcases (by omega : S % 2 ^ d = 0 ∨ S % 2 ^ d = 1) with h | h <;> rw [h] <;> simp
  | succ b ih =>
    intro S hS
    have e : S * y = 2 ^ d * (S / 2 ^ d * y) + S % 2 ^ d * y := by
      conv_lhs => rw [← Nat.div_add_mod S (2 ^ d)]
      ring
    have h0 := hS0 S hS
    have hlt : S % 2 ^ d * y < 2 ^ d := by
      rcases (by omega : S % 2 ^ d = 0 ∨ S % 2 ^ d = 1) with h | h <;> rw [h] <;> omega
    have hS' : ∀ i, (S / 2 ^ d).testBit i = true → d ∣ i := by
      intro i hi
      rw [Nat.testBit_div_two_pow] at hi
      have := hS _ hi
      exact (Nat.dvd_add_right (dvd_refl d)).1 (by rw [Nat.add_comm]; exact this)
    have h1 : ¬ d * (b + 1) + k < d := by
      have := Nat.le_mul_of_pos_right d (by omega : 0 < b + 1)
      omega
    have e1 : d * (b + 1) + k - d = d * b + k := by rw [Nat.mul_succ]; omega
    rw [e, Nat.testBit_two_pow_mul_add _ hlt, ite_eq_right h1, e1, ih _ hS']
    rw [Nat.testBit_div_two_pow]
    rfl

theorem spread_mul3' {d : Nat} (hd : 0 < d) {y S : Nat} (hy : y < 2 ^ d)
    (hS : ∀ i, S.testBit i = true → d ∣ i) (u : Nat) :
    (S * y).testBit u = (S.testBit (d * (u / d)) && y.testBit (u % d)) := by
  have e := Nat.div_add_mod u d
  conv_lhs => rw [← e]
  exact spread_mul3 hd hy _ (Nat.mod_lt _ hd) _ S hS

@[expose] noncomputable def colA (CI X k : Nat) : Nat := Nat.land (Nat.shiftRight X k) CI

@[expose] noncomputable def rowB (d RM X k : Nat) : Nat := Nat.land (Nat.shiftRight X (Nat.mul d k)) RM

theorem colA_dvd {d X k u : Nat} (hd : 0 < d) (h : (colA (rep1 d d) X k).testBit u = true) :
    d ∣ u := by
  unfold colA at h
  rw [land_eq3, shr_eq3, Nat.testBit_and, Bool.and_eq_true] at h
  obtain ⟨c, -, rfl⟩ := (rep1_testBit hd d u).1 h.2
  exact Dvd.intro c rfl

theorem colA_at {d X k i : Nat} (hd : 0 < d) :
    (colA (rep1 d d) X k).testBit (d * i) = (X.testBit (k + d * i) && decide (i < d)) := by
  unfold colA
  rw [land_eq3, shr_eq3, Nat.testBit_and, Nat.testBit_shiftRight]
  congr 1
  apply Bool.eq_iff_iff.2
  rw [rep1_testBit hd, decide_eq_true_iff]
  constructor
  · rintro ⟨c, hc, e⟩
    rw [Nat.eq_of_mul_eq_mul_left hd e]
    exact hc
  · intro hi
    exact ⟨i, hi, rfl⟩

theorem rowB_lt {d X k : Nat} : rowB d (2 ^ d - 1) X k < 2 ^ d := by
  unfold rowB
  rw [land_eq3, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos d)

theorem rowB_at {d X k j : Nat} (hj : j < d) :
    (rowB d (2 ^ d - 1) X k).testBit j = X.testBit (d * k + j) := by
  unfold rowB
  rw [land_eq3, Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_mod_two_pow, shr_eq3, mul_eq3,
    Nat.testBit_shiftRight]
  simp [hj]

theorem prod_at {d X Y k u : Nat} (hd : 0 < d) :
    (colA (rep1 d d) X k * rowB d (2 ^ d - 1) Y k).testBit u =
      ((X.testBit (k + d * (u / d)) && decide (u / d < d)) && Y.testBit (d * k + u % d)) := by
  rw [spread_mul3' hd rowB_lt (fun i h => colA_dvd hd h), colA_at hd,
    rowB_at (Nat.mod_lt _ hd)]

theorem step_tbl : ∀ x1 x2 a1 a2 b1 b2 : Bool, (x1 && x2) = false → (a1 && a2) = false →
    (b1 && b2) = false →
    ((((x2 || ((a1 && b2) || (a2 && b1))) ^^ ((x1 || ((a1 && b2) || (a2 && b1))) ^^
        (x2 || ((a1 && b1) || (a2 && b2))))) &&
      ((x1 || ((a1 && b1) || (a2 && b2))) ^^ ((x1 || ((a1 && b2) || (a2 && b1))) ^^
        (x2 || ((a1 && b1) || (a2 && b2)))))) = false) ∧
    bv ((x2 || ((a1 && b2) || (a2 && b1))) ^^ ((x1 || ((a1 && b2) || (a2 && b1))) ^^
        (x2 || ((a1 && b1) || (a2 && b2)))))
      ((x1 || ((a1 && b1) || (a2 && b2))) ^^ ((x1 || ((a1 && b2) || (a2 && b1))) ^^
        (x2 || ((a1 && b1) || (a2 && b2))))) = bv x1 x2 + bv a1 a2 * bv b1 b2 := by
  decide

@[expose] def LoopInv (d N A1 A2 B1 B2 k x1 x2 : Nat) : Prop :=
  (∀ u, (x1.testBit u && x2.testBit u) = false) ∧
  (∀ u, N ≤ u → x1.testBit u = false ∧ x2.testBit u = false) ∧
  ∀ i < d, ∀ j < d, bv (x1.testBit (d * i + j)) (x2.testBit (d * i + j)) =
    ∑ l ∈ Finset.range k, bv (A1.testBit (l + d * i)) (A2.testBit (l + d * i)) *
      bv (B1.testBit (d * l + j)) (B2.testBit (d * l + j))

theorem mulLoop3_succ (d N CI RM A1 A2 B1 B2 n k x1 x2 : Nat) :
    mulLoop3 d N CI RM A1 A2 B1 B2 (n + 1) k x1 x2 =
      mulLoop3 d N CI RM A1 A2 B1 B2 n (k + 1)
        ((x2 ||| (colA CI A1 k * rowB d RM B2 k + colA CI A2 k * rowB d RM B1 k)) ^^^
          ((x1 ||| (colA CI A1 k * rowB d RM B2 k + colA CI A2 k * rowB d RM B1 k)) ^^^
            (x2 ||| (colA CI A1 k * rowB d RM B1 k + colA CI A2 k * rowB d RM B2 k))))
        ((x1 ||| (colA CI A1 k * rowB d RM B1 k + colA CI A2 k * rowB d RM B2 k)) ^^^
          ((x1 ||| (colA CI A1 k * rowB d RM B2 k + colA CI A2 k * rowB d RM B1 k)) ^^^
            (x2 ||| (colA CI A1 k * rowB d RM B1 k + colA CI A2 k * rowB d RM B2 k)))) := by
  change strictN _ (fun z1 => strictN _ (fun z2 => mulLoop3 d N CI RM A1 A2 B1 B2 n (k + 1) z1 z2)) = _
  rw [strictN_eq3, strictN_eq3]
  rfl

theorem loop_step {d N A1 A2 B1 B2 k x1 x2 : Nat} (hd : 0 < d) (hN : N = d * d)
    (hA : ∀ u, (A1.testBit u && A2.testBit u) = false)
    (hB : ∀ u, (B1.testBit u && B2.testBit u) = false)
    (h : LoopInv d N A1 A2 B1 B2 k x1 x2) :
    LoopInv d N A1 A2 B1 B2 (k + 1)
      ((x2 ||| (colA (rep1 d d) A1 k * rowB d (2 ^ d - 1) B2 k +
          colA (rep1 d d) A2 k * rowB d (2 ^ d - 1) B1 k)) ^^^
        ((x1 ||| (colA (rep1 d d) A1 k * rowB d (2 ^ d - 1) B2 k +
            colA (rep1 d d) A2 k * rowB d (2 ^ d - 1) B1 k)) ^^^
          (x2 ||| (colA (rep1 d d) A1 k * rowB d (2 ^ d - 1) B1 k +
            colA (rep1 d d) A2 k * rowB d (2 ^ d - 1) B2 k))))
      ((x1 ||| (colA (rep1 d d) A1 k * rowB d (2 ^ d - 1) B1 k +
          colA (rep1 d d) A2 k * rowB d (2 ^ d - 1) B2 k)) ^^^
        ((x1 ||| (colA (rep1 d d) A1 k * rowB d (2 ^ d - 1) B2 k +
            colA (rep1 d d) A2 k * rowB d (2 ^ d - 1) B1 k)) ^^^
          (x2 ||| (colA (rep1 d d) A1 k * rowB d (2 ^ d - 1) B1 k +
            colA (rep1 d d) A2 k * rowB d (2 ^ d - 1) B2 k)))) := by
  obtain ⟨hx, hhi, hv⟩ := h
  have hq : ∀ u, (colA (rep1 d d) A1 k * rowB d (2 ^ d - 1) B1 k +
      colA (rep1 d d) A2 k * rowB d (2 ^ d - 1) B2 k).testBit u =
      (((A1.testBit (k + d * (u / d)) && decide (u / d < d)) && B1.testBit (d * k + u % d)) ||
        ((A2.testBit (k + d * (u / d)) && decide (u / d < d)) && B2.testBit (d * k + u % d))) := by
    intro u
    rw [testBit_add_disj (fun p hp => by
      rw [prod_at hd, prod_at hd] at hp
      have := hA (k + d * (p / d))
      revert hp this
      cases A1.testBit (k + d * (p / d)) <;> cases A2.testBit (k + d * (p / d)) <;> simp), prod_at hd,
      prod_at hd]
  have hm : ∀ u, (colA (rep1 d d) A1 k * rowB d (2 ^ d - 1) B2 k +
      colA (rep1 d d) A2 k * rowB d (2 ^ d - 1) B1 k).testBit u =
      (((A1.testBit (k + d * (u / d)) && decide (u / d < d)) && B2.testBit (d * k + u % d)) ||
        ((A2.testBit (k + d * (u / d)) && decide (u / d < d)) && B1.testBit (d * k + u % d))) := by
    intro u
    rw [testBit_add_disj (fun p hp => by
      rw [prod_at hd, prod_at hd] at hp
      have := hA (k + d * (p / d))
      revert hp this
      cases A1.testBit (k + d * (p / d)) <;> cases A2.testBit (k + d * (p / d)) <;> simp), prod_at hd,
      prod_at hd]
  have ha : ∀ u, ((A1.testBit (k + d * (u / d)) && decide (u / d < d)) &&
      (A2.testBit (k + d * (u / d)) && decide (u / d < d))) = false := by
    intro u
    have := hA (k + d * (u / d))
    revert this
    cases A1.testBit (k + d * (u / d)) <;> cases A2.testBit (k + d * (u / d)) <;> simp
  refine ⟨fun u => ?_, fun u hu => ?_, fun i hi j hj => ?_⟩
  · simp only [Nat.testBit_xor, Nat.testBit_or, hq, hm]
    exact (step_tbl _ _ _ _ _ _ (hx u) (ha u) (hB _)).1
  · have hud : d ≤ u / d := (Nat.le_div_iff_mul_le hd).2 (by rw [hN] at hu; exact hu)
    have hn : decide (u / d < d) = false := by simp; omega
    simp only [Nat.testBit_xor, Nat.testBit_or, hq, hm, hn, Bool.and_false, Bool.false_and,
      Bool.or_false, (hhi u hu).1, (hhi u hu).2]
    decide
  · have e := dm_eq3 (i := i) hj
    simp only [Nat.testBit_xor, Nat.testBit_or, hq, hm, e.1, e.2, hi, decide_true, Bool.and_true]
    rw [(step_tbl _ _ _ _ _ _ (hx _) (by have := hA (k + d * i); simpa using this) (hB _)).2,
      hv i hi j hj, Finset.sum_range_succ]

theorem loop_sound {d N A1 A2 B1 B2 : Nat} (hd : 0 < d) (hN : N = d * d)
    (hA : ∀ u, (A1.testBit u && A2.testBit u) = false)
    (hB : ∀ u, (B1.testBit u && B2.testBit u) = false) :
    ∀ n k x1 x2, k + n = d → LoopInv d N A1 A2 B1 B2 k x1 x2 →
      Canon3 N (mulLoop3 d N (rep1 d d) (2 ^ d - 1) A1 A2 B1 B2 n k x1 x2) ∧
      ∀ i < d, ∀ j < d,
        bv ((mulLoop3 d N (rep1 d d) (2 ^ d - 1) A1 A2 B1 B2 n k x1 x2).testBit (d * i + j))
          ((mulLoop3 d N (rep1 d d) (2 ^ d - 1) A1 A2 B1 B2 n k x1 x2).testBit (N + (d * i + j))) =
        ∑ l ∈ Finset.range d, bv (A1.testBit (l + d * i)) (A2.testBit (l + d * i)) *
          bv (B1.testBit (d * l + j)) (B2.testBit (d * l + j)) := by
  intro n
  induction n with
  | zero =>
    intro k x1 x2 hk h
    rw [Nat.add_zero] at hk
    subst k
    obtain ⟨hx, hhi, hv⟩ := h
    have hx1 : x1 < 2 ^ N := Nat.lt_pow_two_of_testBit x1 (fun u hu => (hhi u hu).1)
    have hx2 : x2 < 2 ^ N := Nat.lt_pow_two_of_testBit x2 (fun u hu => (hhi u hu).2)
    have e : mulLoop3 d N (rep1 d d) (2 ^ d - 1) A1 A2 B1 B2 0 d x1 x2 = 2 ^ N * x2 + x1 := by
      change x1 + x2 <<< N = _
      rw [Nat.shiftLeft_eq, Nat.add_comm, Nat.mul_comm]
    have hbit : ∀ u, (2 ^ N * x2 + x1).testBit u = if u < N then x1.testBit u else x2.testBit (u - N) :=
      fun u => Nat.testBit_two_pow_mul_add _ hx1 u
    rw [e]
    refine ⟨⟨?_, fun t ht => ?_⟩, fun i hi j hj => ?_⟩
    · have : 2 ^ (N + N) = 2 ^ N * 2 ^ N := Nat.pow_add 2 N N
      rw [this]
      have := Nat.mul_le_mul_left (2 ^ N) (Nat.succ_le_of_lt hx2)
      rw [Nat.mul_succ] at this
      omega
    · rw [hbit, ite_eq_right (by omega), Nat.add_sub_cancel_left]
      rw [hbit] at ht
      by_cases htN : t < N
      · rw [ite_eq_left htN] at ht
        have := hx t
        rw [ht] at this
        simpa using this
      · exact (hhi t (by omega)).2
    · have hlt : d * i + j < N := hN ▸ idx_lt3 hi hj
      rw [hbit, hbit, ite_eq_left hlt, ite_eq_right (by omega), Nat.add_sub_cancel_left]
      exact hv i hi j hj
  | succ n ih =>
    intro k x1 x2 hk h
    rw [mulLoop3_succ]
    exact ih (k + 1) _ _ (by omega) (loop_step hd hN hA hB h)

theorem lo_bit {N X t : Nat} : (X &&& (2 ^ N - 1)).testBit t = (decide (t < N) && X.testBit t) := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_mod_two_pow]

theorem mul3s_sound {d f N LO RM CI ONE UP A B : Nat} (hc : consts3OK d f N LO RM CI ONE UP = true)
    (hA : Canon3 N A) (hB : Canon3 N B) :
    Canon3 N (mul3s d N LO CI RM A B) ∧ mat3 d N (mul3s d N LO CI RM A B) = mat3 d N A * mat3 d N B := by
  obtain ⟨hd, hN, hLO, hRM, hCI, -⟩ := consts3_facts hc
  subst hLO hRM hCI
  have e : mul3s d N (2 ^ N - 1) (rep1 d d) (2 ^ d - 1) A B =
      mulLoop3 d N (rep1 d d) (2 ^ d - 1) (A &&& (2 ^ N - 1)) (A >>> N) (B &&& (2 ^ N - 1)) (B >>> N)
        d 0 0 0 := by
    unfold mul3s
    rw [strictN_eq3, strictN_eq3, strictN_eq3, strictN_eq3]
    rfl
  have hdj : ∀ {X : Nat}, Canon3 N X → ∀ u, ((X &&& (2 ^ N - 1)).testBit u && (X >>> N).testBit u) = false := by
    intro X hX u
    rw [lo_bit, Nat.testBit_shiftRight]
    cases h : X.testBit u
    · simp
    · rw [hX.2 u h]
      simp
  have h0 : LoopInv d N (A &&& (2 ^ N - 1)) (A >>> N) (B &&& (2 ^ N - 1)) (B >>> N) 0 0 0 :=
    ⟨fun u => by simp, fun u _ => by simp, fun i _ j _ => by simp [bv]⟩
  obtain ⟨hcan, hval⟩ := loop_sound hd hN (hdj hA) (hdj hB) d 0 0 0 (Nat.zero_add d) h0
  rw [e]
  refine ⟨hcan, ?_⟩
  funext i j
  rw [Matrix.mul_apply]
  change bv _ _ = _
  rw [hval i.val i.isLt j.val j.isLt, Finset.sum_range (fun l => _)]
  apply Finset.sum_congr rfl
  intro l _
  have h1 : d * i.val + l.val < N := hN ▸ idx_lt3 i.isLt l.isLt
  have h2 : d * l.val + j.val < N := hN ▸ idx_lt3 l.isLt j.isLt
  unfold mat3
  rw [lo_bit, lo_bit, Nat.testBit_shiftRight, Nat.testBit_shiftRight, Nat.add_comm l.val,
    decide_eq_true h1, decide_eq_true h2, Bool.true_and, Bool.true_and]

theorem one3_sound {d f N LO RM CI ONE UP : Nat} (hc : consts3OK d f N LO RM CI ONE UP = true) :
    Canon3 N ONE ∧ mat3 d N ONE = 1 := by
  obtain ⟨hd, hN, -, -, -, hONE⟩ := consts3_facts hc
  subst hONE
  have hbit := rep1_testBit (s := d + 1) (by omega) d
  have hlow : ∀ u, N ≤ u → (rep1 (d + 1) d).testBit u = false := by
    intro u hu
    cases h : (rep1 (d + 1) d).testBit u
    · rfl
    · obtain ⟨c, hc, rfl⟩ := (hbit _).1 h
      have : (d + 1) * c ≤ (d + 1) * (d - 1) := Nat.mul_le_mul_left _ (by omega)
      have e : (d + 1) * (d - 1) + 1 = d * d := by
        obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring
      omega
  refine ⟨⟨?_, fun t _ => hlow _ (by omega)⟩, ?_⟩
  · exact Nat.lt_of_lt_of_le (Nat.lt_pow_two_of_testBit _ hlow)
      (Nat.pow_le_pow_right (by omega) (by omega))
  funext i j
  unfold mat3
  rw [hlow (N + (d * i.val + j.val)) (by omega), Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    have : (rep1 (d + 1) d).testBit (d * i.val + i.val) = true :=
      (hbit _).2 ⟨i.val, i.isLt, by ring⟩
    rw [this, ite_eq_left rfl]
    rfl
  · have : (rep1 (d + 1) d).testBit (d * i.val + j.val) = false := by
      cases h : (rep1 (d + 1) d).testBit (d * i.val + j.val)
      · rfl
      · exfalso
        obtain ⟨c, hc, e⟩ := (hbit _).1 h
        apply hij
        have hi := i.isLt
        have hj := j.isLt
        rcases lt_trichotomy i.val c with h1 | h1 | h1
        · have := Nat.mul_le_mul_left d (Nat.succ_le_of_lt h1)
          rw [Nat.mul_succ] at this
          have : (d + 1) * c = d * c + c := by ring
          omega
        · subst h1
          apply Fin.ext
          have : (d + 1) * i.val = d * i.val + i.val := by ring
          omega
        · have := Nat.mul_le_mul_left d (Nat.succ_le_of_lt h1)
          rw [Nat.mul_succ] at this
          have : (d + 1) * c = d * c + c := by ring
          omega
    rw [this, ite_eq_right hij]
    rfl

theorem bv_inj : ∀ x1 x2 y1 y2 : Bool, (x1 && x2) = false → (y1 && y2) = false →
    bv x1 x2 = bv y1 y2 → x1 = y1 ∧ x2 = y2 := by
  decide

theorem mat3_inj {d N X Y : Nat} (hN : N = d * d) (hX : Canon3 N X) (hY : Canon3 N Y)
    (h : mat3 d N X = mat3 d N Y) : X = Y := by
  have hdj : ∀ {Z : Nat}, Canon3 N Z → ∀ t, (Z.testBit t && Z.testBit (N + t)) = false := by
    intro Z hZ t
    cases h : Z.testBit t
    · rfl
    · rw [hZ.2 t h]
      rfl
  have hent : ∀ t < N, X.testBit t = Y.testBit t ∧ X.testBit (N + t) = Y.testBit (N + t) := by
    intro t ht
    have hd : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · subst h0
        simp at hN
        omega
      · exact h0
    have hti : t / d < d := (Nat.div_lt_iff_lt_mul hd).2 (by rw [hN] at ht; exact ht)
    have htj : t % d < d := Nat.mod_lt _ hd
    have e : d * (t / d) + t % d = t := Nat.div_add_mod t d
    have := congrFun (congrFun h ⟨t / d, hti⟩) ⟨t % d, htj⟩
    unfold mat3 at this
    simp only [e] at this
    exact bv_inj _ _ _ _ (hdj hX t) (hdj hY t) this
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases h1 : t < N
  · exact (hent t h1).1
  · by_cases h2 : t < N + N
    · have := (hent (t - N) (by omega)).2
      rwa [Nat.add_sub_cancel' (by omega)] at this
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hX.1 (Nat.pow_le_pow_right (by omega) (by omega))),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hY.1 (Nat.pow_le_pow_right (by omega) (by omega)))]

end CFSG.KS.Mat3

end
