module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDefs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.GH74.GLS.Stage4.Rest

namespace Mix11cN

@[expose] def dg (p A i : ℕ) : ℕ := A / p ^ i % p

theorem dg_succ (p A i : ℕ) : dg p A (i + 1) = dg p (A / p) i := by
  simp [dg, pow_succ, Nat.div_div_eq_div_mul, mul_comm]

theorem sum_dg {p : ℕ} (hp : 1 < p) {n : ℕ} {A : ℕ} (hA : A < p ^ n) :
    A = ∑ i ∈ Finset.range n, dg p A i * p ^ i := by
  induction n generalizing A with
  | zero =>
    simp at hA
    simp [hA]
  | succ n ih =>
    have hA' : A / p < p ^ n := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      simpa [pow_succ, mul_comm] using hA
    rw [Finset.sum_range_succ']
    have h2 : ∑ i ∈ Finset.range n, dg p A (i + 1) * p ^ (i + 1) =
        p * ∑ i ∈ Finset.range n, dg p (A / p) i * p ^ i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [dg_succ]
      ring
    rw [h2, ← ih hA']
    simp only [dg, pow_zero, Nat.div_one, mul_one]
    exact (Nat.div_add_mod A p).symm

theorem eq_of_dg_eq {p : ℕ} (hp : 1 < p) {n A B : ℕ} (hA : A < p ^ n) (hB : B < p ^ n)
    (h : ∀ i, i < n → dg p A i = dg p B i) : A = B := by
  rw [sum_dg hp hA, sum_dg hp hB]
  exact Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]

section Rot

variable {p : ℕ}

theorem rot_succ_eq (m A : ℕ) : rot p (m + 1) A = (A % p ^ m) * p + A / p ^ m := by
  simp [rot]

theorem div_pow_lt (hp : 1 < p) {m A : ℕ} (hA : A < p ^ (m + 1)) : A / p ^ m < p := by
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  simpa [pow_succ, mul_comm] using hA

theorem rot_lt (hp : 1 < p) {m A : ℕ} (hA : A < p ^ (m + 1)) : rot p (m + 1) A < p ^ (m + 1) := by
  rw [rot_succ_eq]
  have h1 : A % p ^ m < p ^ m := Nat.mod_lt _ (by positivity)
  have h2 := div_pow_lt hp hA
  calc (A % p ^ m) * p + A / p ^ m < (A % p ^ m) * p + p := by omega
    _ = (A % p ^ m + 1) * p := by ring
    _ ≤ p ^ m * p := Nat.mul_le_mul_right _ h1
    _ = p ^ (m + 1) := by ring

theorem dg_rot_zero (m A : ℕ) : dg p (rot p (m + 1) A) 0 = dg p A m := by
  rw [rot_succ_eq]
  simp [dg]

theorem mod_pow_div_mod {m i : ℕ} (hi : i < m) (A : ℕ) :
    A % p ^ m / p ^ i % p = A / p ^ i % p := by
  have hm : p ^ m = p ^ i * p ^ (m - i) := by rw [← pow_add]; congr 1; omega
  rw [hm, Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ (dvd_pow_self p (by omega))

theorem dg_rot_succ (hp : 1 < p) {m A : ℕ} (hA : A < p ^ (m + 1)) {i : ℕ} (hi : i < m) :
    dg p (rot p (m + 1) A) (i + 1) = dg p A i := by
  have hY := div_pow_lt hp hA
  have hdiv : rot p (m + 1) A / p = A % p ^ m := by
    rw [rot_succ_eq, mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hY, add_zero]
  rw [dg_succ, hdiv]
  exact mod_pow_div_mod hi A

theorem dg_rot_shift (hp : 1 < p) {m A : ℕ} (hA : A < p ^ (m + 1)) {i : ℕ} (hi : i < m + 1) :
    dg p (rot p (m + 1) A) ((i + 1) % (m + 1)) = dg p A i := by
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with him | rfl
  · rw [Nat.mod_eq_of_lt (by omega)]
    exact dg_rot_succ hp hA him
  · rw [Nat.mod_self]
    exact dg_rot_zero _ _

theorem iterate_rot_lt (hp : 1 < p) {m A : ℕ} (hA : A < p ^ (m + 1)) (s : ℕ) :
    (rot p (m + 1))^[s] A < p ^ (m + 1) := by
  induction s with
  | zero => simpa using hA
  | succ s ih =>
    rw [Function.iterate_succ_apply']
    exact rot_lt hp ih

theorem dg_iterate_rot (hp : 1 < p) {m A : ℕ} (hA : A < p ^ (m + 1)) (s : ℕ) {i : ℕ}
    (hi : i < m + 1) : dg p ((rot p (m + 1))^[s] A) ((i + s) % (m + 1)) = dg p A i := by
  induction s with
  | zero => simp [Nat.mod_eq_of_lt hi]
  | succ s ih =>
    rw [Function.iterate_succ_apply']
    have h1 := dg_rot_shift hp (iterate_rot_lt hp hA s) (Nat.mod_lt (i + s) (by omega))
    rw [← ih, ← h1]
    congr 1
    rw [Nat.mod_add_mod, add_assoc]

theorem iterate_rot_period (hp : 1 < p) {m A : ℕ} (hA : A < p ^ (m + 1)) :
    (rot p (m + 1))^[m + 1] A = A := by
  refine eq_of_dg_eq hp (iterate_rot_lt hp hA _) hA fun i hi => ?_
  have := dg_iterate_rot hp hA (m + 1) hi
  rwa [Nat.add_mod_right, Nat.mod_eq_of_lt hi] at this

end Rot

section Orbit

variable {p : ℕ}

theorem rotPeriod_dvd (hp : 1 < p) {m A : ℕ} (hA : A < p ^ (m + 1)) :
    rotPeriod p (m + 1) A ∣ m + 1 :=
  Function.IsPeriodicPt.minimalPeriod_dvd (iterate_rot_period hp hA)

theorem rotPeriod_pos (hp : 1 < p) {m A : ℕ} (hA : A < p ^ (m + 1)) :
    0 < rotPeriod p (m + 1) A :=
  Function.IsPeriodicPt.minimalPeriod_pos (Nat.succ_pos m) (iterate_rot_period hp hA)

theorem iterate_rotPeriod (m A p : ℕ) :
    (rot p (m + 1))^[rotPeriod p (m + 1) A] A = A :=
  Function.iterate_minimalPeriod

theorem dg_period (hp : 1 < p) {m A : ℕ} (hA : A < p ^ (m + 1)) (i : ℕ) :
    dg p A ((i + rotPeriod p (m + 1) A) % (m + 1)) = dg p A (i % (m + 1)) := by
  have h := dg_iterate_rot hp hA (rotPeriod p (m + 1) A) (Nat.mod_lt i (Nat.succ_pos m))
  rw [iterate_rotPeriod, Nat.mod_add_mod] at h
  exact h

theorem prod_range_period {f : ℕ → ℕ} {r : ℕ} (hf : ∀ i, f (i + r) = f i) (t : ℕ) :
    ∏ i ∈ Finset.range (r * t), f i = (∏ i ∈ Finset.range r, f i) ^ t := by
  have hk : ∀ k i, f (i + r * k) = f i := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => intro i; rw [mul_add, mul_one, ← add_assoc, hf, ih]
  induction t with
  | zero => simp
  | succ t ih =>
    rw [mul_add, mul_one, Finset.prod_range_add, ih, pow_succ]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [add_comm, hk]

theorem sum_range_period {f : ℕ → ℕ} {r : ℕ} (hf : ∀ i, f (i + r) = f i) (t : ℕ) :
    ∑ i ∈ Finset.range (r * t), f i * p ^ i =
      (∑ k ∈ Finset.range t, p ^ (r * k)) * ∑ i ∈ Finset.range r, f i * p ^ i := by
  have hk : ∀ k i, f (i + r * k) = f i := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => intro i; rw [mul_add, mul_one, ← add_assoc, hf, ih]
  induction t with
  | zero => simp
  | succ t ih =>
    rw [mul_add, mul_one, Finset.sum_range_add, ih, Finset.sum_range_succ, add_mul]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_comm, hk, pow_add]
    ring

end Orbit

section Prod

variable {p : ℕ}

theorem digitProd_eq_pow (hp : 1 < p) {m A : ℕ} (hA : A < p ^ (m + 1)) :
    digitProd p (m + 1) A =
      (∏ i ∈ Finset.range (rotPeriod p (m + 1) A), (dg p A i + 1)) ^
        ((m + 1) / rotPeriod p (m + 1) A) := by
  have hdvd : rotPeriod p (m + 1) A ∣ m + 1 := rotPeriod_dvd hp hA
  have hpos : 0 < rotPeriod p (m + 1) A := rotPeriod_pos hp hA
  generalize hr : rotPeriod p (m + 1) A = r at hdvd hpos ⊢
  obtain ⟨t, ht⟩ := hdvd
  have hrt : (m + 1) / r = t := by rw [ht]; exact Nat.mul_div_cancel_left t hpos
  rw [hrt]
  have hf : ∀ i, (fun i => dg p A (i % (m + 1)) + 1) (i + r) = (fun i => dg p A (i % (m + 1)) + 1) i := by
    intro i
    have := dg_period hp hA i
    rw [hr] at this
    simp only [this]
  have h1 : digitProd p (m + 1) A = ∏ i ∈ Finset.range (r * t), (dg p A (i % (m + 1)) + 1) := by
    rw [← ht]
    unfold digitProd
    refine Finset.prod_congr rfl fun i hi => ?_
    show dg p A i + 1 = dg p A (i % (m + 1)) + 1
    rw [Nat.mod_eq_of_lt (Finset.mem_range.1 hi)]
  rw [h1, prod_range_period hf t]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  have : i < m + 1 := lt_of_lt_of_le (Finset.mem_range.1 hi) (Nat.le_of_dvd (Nat.succ_pos m) ⟨t, ht⟩)
  rw [Nat.mod_eq_of_lt this]

theorem exists_dg_ne_zero (hp : 1 < p) {n A : ℕ} (hA : A < p ^ n) (hA0 : A ≠ 0) :
    ∃ i < n, dg p A i ≠ 0 := by
  by_contra h
  have h' : ∀ i < n, dg p A i = 0 := fun i hi => by
    by_contra hne
    exact h ⟨i, hi, hne⟩
  apply hA0
  rw [sum_dg hp hA]
  exact Finset.sum_eq_zero fun i hi => by rw [h' i (Finset.mem_range.1 hi)]; simp

theorem two_le_digitProd (hp : 1 < p) {n A : ℕ} (hA : A < p ^ n) (hA0 : A ≠ 0) :
    2 ≤ digitProd p n A := by
  obtain ⟨i, hi, hne⟩ := exists_dg_ne_zero hp hA hA0
  have hpos : 0 < digitProd p n A := Finset.prod_pos fun j _ => Nat.succ_pos _
  have hdvd : dg p A i + 1 ∣ digitProd p n A :=
    Finset.dvd_prod_of_mem (fun j => A / p ^ j % p + 1) (Finset.mem_range.2 hi)
  have := Nat.le_of_dvd hpos hdvd
  omega

theorem period_structure (hp : 1 < p) {m A : ℕ} (hA : A < p ^ (m + 1)) (hA0 : A ≠ 0) :
    ∃ r t P : ℕ, rotPeriod p (m + 1) A = r ∧ m + 1 = r * t ∧ 0 < r ∧ 0 < t ∧ 2 ≤ P ∧
      digitProd p (m + 1) A = P ^ t ∧ ∏ i ∈ Finset.range r, (dg p A i + 1) = P := by
  have hdvd : rotPeriod p (m + 1) A ∣ m + 1 := rotPeriod_dvd hp hA
  have hpos : 0 < rotPeriod p (m + 1) A := rotPeriod_pos hp hA
  have hD := digitProd_eq_pow hp hA
  have h2 := two_le_digitProd hp hA hA0
  generalize hr : rotPeriod p (m + 1) A = r at hdvd hpos hD ⊢
  obtain ⟨t, ht⟩ := hdvd
  have hrt : (m + 1) / r = t := by rw [ht]; exact Nat.mul_div_cancel_left t hpos
  rw [hrt] at hD
  have htpos : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · rw [h0] at ht; omega
    · exact h0
  refine ⟨r, t, ∏ i ∈ Finset.range r, (dg p A i + 1), rfl, ht, hpos, htpos, ?_, hD, rfl⟩
  by_contra hlt
  have hlt := not_le.1 hlt
  have hle : (∏ i ∈ Finset.range r, (dg p A i + 1)) ≤ 1 := by omega
  have : (∏ i ∈ Finset.range r, (dg p A i + 1)) ^ t ≤ 1 := pow_le_one₀ (Nat.zero_le _) hle
  omega

end Prod

end Mix11cN

end CFSG.GH74.GLS.Stage4.Rest
