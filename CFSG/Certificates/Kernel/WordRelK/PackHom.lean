module

public import Certificates.Data.Kernel.PauliPack
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Tactic.TypeStar

public section

namespace CFSG.KC.WordRelK

open CFSG.Monster.B

theorem allBelow_true {n : Nat} {f : Nat → Bool} (h : allBelow n f = true) :
    ∀ k < n, f k = true := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    have h' : (allBelow n f && f n) = true := h
    rw [Bool.and_eq_true] at h'
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact ih h'.1 k hk
    · exact h'.2

private theorem par12_all : allBelow 64 (fun h => allBelow 64 fun l =>
    Nat.beq (par12 (64 * h + l)) (if Model.parN 12 (64 * h + l) then 1 else 0)) = true := by
  decide +kernel

theorem par12_eq : ∀ v < 4096, par12 v = if Model.parN 12 v then 1 else 0 := by
  intro v hv
  have h := allBelow_true (allBelow_true par12_all (v / 64) (by omega)) (v % 64) (by omega)
  rw [Nat.div_add_mod] at h
  exact Nat.eq_of_beq_eq_true h

theorem beq_div_mod (n : Nat) : Nat.beq (n / 16777216 % 2) 1 = n.testBit 24 := by
  rw [Nat.testBit_eq_decide_div_mod_eq, show (2 : Nat) ^ 24 = 16777216 from rfl]
  rcases Nat.mod_two_eq_zero_or_one (n / 16777216) with h | h <;> rw [h] <;> rfl

private theorem bit24 (b : Bool) (i : Nat) :
    ((if b then 1 else 0) * 16777216).testBit i = (b && decide (i = 24)) := by
  cases b
  · simp
  · rw [show (if true then 1 else 0) * 16777216 = 2 ^ 24 from rfl, Nat.testBit_two_pow]
    simp [eq_comm]

theorem unpackP_mulP (x y : Nat) : unpackP (mulP x y) = (unpackP x).mul (unpackP y) := by
  have hv : (y % 4096) &&& (x / 4096 % 4096) < 4096 :=
    Nat.and_lt_two_pow (n := 12) _ (Nat.mod_lt _ (by decide))
  unfold mulP
  rw [par12_eq _ hv]
  generalize hb : Model.parN 12 ((y % 4096) &&& (x / 4096 % 4096)) = b
  have hpair : Model.pairN (y % 4096) (x / 4096 % 4096) = b := hb
  simp only [unpackP, Model.Pauli.mul, Model.Pauli.s, Model.Pauli.a, Model.Pauli.d, hpair,
    beq_div_mod]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [Nat.testBit_xor, bit24]
    simp
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [show (4096 : Nat) = 2 ^ 12 from rfl]
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor, bit24]
    by_cases hi : i < 12
    · simp [hi, show i ≠ 24 by omega]
    · simp [hi]
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [show (4096 : Nat) = 2 ^ 12 from rfl]
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_xor, bit24]
    by_cases hi : i < 12
    · simp [hi, show i + 12 ≠ 24 by omega]
    · simp [hi]

theorem mulP_lt {x y : Nat} (hx : x < 2 ^ 25) (hy : y < 2 ^ 25) : mulP x y < 2 ^ 25 := by
  unfold mulP
  refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hx hy) ?_
  have h := Nat.mod_two_eq_zero_or_one (foldX 1 (foldX 2 (foldX 4 (foldX 8
    ((y % 4096) &&& (x / 4096 % 4096))))))
  unfold par12
  rcases h with h | h <;> rw [h] <;> decide

private theorem pairN_zero_right (a : Nat) : Model.pairN a 0 = false := by
  simp only [Model.pairN, Nat.and_zero]
  rfl

private theorem pairN_zero_left (d : Nat) : Model.pairN 0 d = false := by
  simp only [Model.pairN, Nat.zero_and]
  rfl

private theorem mul_T (u t : Nat) :
    Model.Pauli.mul (false, u, 0) (false, t, 0) = (false, u ^^^ t, 0) := by
  simp only [Model.Pauli.mul, Model.Pauli.s, Model.Pauli.a, Model.Pauli.d, pairN_zero_right,
    Bool.xor_false, Nat.xor_zero]

private theorem mul_D (u t : Nat) :
    Model.Pauli.mul (false, 0, u) (false, 0, t) = (false, 0, u ^^^ t) := by
  simp only [Model.Pauli.mul, Model.Pauli.s, Model.Pauli.a, Model.Pauli.d, pairN_zero_left,
    Bool.xor_false, Nat.xor_zero]

private theorem mul_split (s : Bool) (a d : Nat) :
    Model.Pauli.mul (Model.Pauli.mul (s, 0, 0) (false, a, 0)) (false, 0, d) = (s, a, d) := by
  simp only [Model.Pauli.mul, Model.Pauli.s, Model.Pauli.a, Model.Pauli.d, pairN_zero_right,
    Bool.xor_false, Nat.zero_xor, Nat.xor_zero]

private theorem mod_two_pow_succ (a n : Nat) :
    a % 2 ^ (n + 1) = a % 2 ^ n ^^^ (if a.testBit n then 2 ^ n else 0) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  split
  · rw [Nat.testBit_two_pow]
    rcases Nat.lt_trichotomy i n with h | rfl | h
    · simp [h, Nat.lt_succ_of_lt h, Nat.ne_of_gt h]
    · simp_all
    · simp [show ¬ i < n + 1 by omega, show ¬ i < n by omega, show n ≠ i by omega]
  · simp only [Nat.zero_testBit, Bool.xor_false]
    rcases Nat.lt_trichotomy i n with h | rfl | h
    · simp [h, Nat.lt_succ_of_lt h]
    · simp_all
    · simp [show ¬ i < n + 1 by omega, show ¬ i < n by omega]

@[expose] def applyN (n acc yb rb : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun acc _ _ => acc)
    (fun _ ih acc yb rb =>
      ih (bif Nat.beq (yb % 2) 1 then mulP acc (rb % 33554432) else acc) (yb / 2)
        (rb / 33554432))
    n acc yb rb

theorem applyRow_eq (row y : Nat) :
    applyRow row y = applyN 24 (y / 16777216 * 16777216) (y % 16777216) row := rfl

theorem applyN_succ (n acc yb rb : Nat) : applyN (n + 1) acc yb rb =
    applyN n (bif Nat.beq (yb % 2) 1 then mulP acc (rb % 33554432) else acc) (yb / 2)
      (rb / 33554432) := rfl

section Hom

variable {G : Type*} [Group G] (φ : Model.Pauli → G)
  (hφ : ∀ x y, φ (Model.Pauli.mul x y) = φ x * φ y)

include hφ

theorem hom_one : φ (false, 0, 0) = 1 := by
  have h : Model.Pauli.mul (false, 0, 0) (false, 0, 0) = (false, 0, 0) := by decide
  have h2 : φ (false, 0, 0) * φ (false, 0, 0) = φ (false, 0, 0) * 1 := by
    rw [mul_one, ← hφ, h]
  exact mul_left_cancel h2

theorem hom_T_decomp (a : Nat) : ∀ n, φ (false, a % 2 ^ n, 0) =
    ((List.range n).map fun k => if a.testBit k then φ (false, 2 ^ k, 0) else 1).prod
  | 0 => by
    rw [pow_zero, Nat.mod_one]
    exact hom_one φ hφ
  | n + 1 => by
    have hb : φ (false, (if a.testBit n then 2 ^ n else 0), 0) =
        if a.testBit n then φ (false, 2 ^ n, 0) else 1 := by
      cases a.testBit n
      · exact hom_one φ hφ
      · rfl
    rw [List.range_succ, List.map_append, List.prod_append, ← hom_T_decomp a n,
      List.map_singleton, List.prod_singleton, ← hb, ← hφ, mul_T, mod_two_pow_succ]

theorem hom_D_decomp (d : Nat) : ∀ n, φ (false, 0, d % 2 ^ n) =
    ((List.range n).map fun k => if d.testBit k then φ (false, 0, 2 ^ k) else 1).prod
  | 0 => by
    rw [pow_zero, Nat.mod_one]
    exact hom_one φ hφ
  | n + 1 => by
    have hb : φ (false, 0, (if d.testBit n then 2 ^ n else 0)) =
        if d.testBit n then φ (false, 0, 2 ^ n) else 1 := by
      cases d.testBit n
      · exact hom_one φ hφ
      · rfl
    rw [List.range_succ, List.map_append, List.prod_append, ← hom_D_decomp d n,
      List.map_singleton, List.prod_singleton, ← hb, ← hφ, mul_D, mod_two_pow_succ]

theorem hom_unpackP_decomp (y : Nat) :
    φ (unpackP y) = φ ((unpackP y).1, 0, 0) *
      ((List.range 24).map fun k =>
        if (y % 16777216).testBit k then φ (basisP k) else 1).prod := by
  have hu : unpackP y = ((unpackP y).1, y % 2 ^ 12, y / 2 ^ 12 % 2 ^ 12) := rfl
  have hT := hom_T_decomp φ hφ y 12
  have hD := hom_D_decomp φ hφ (y / 2 ^ 12) 12
  have h1 : ((List.range 12).map fun k => if y.testBit k then φ (false, 2 ^ k, 0) else 1) =
      (List.range 12).map fun k => if (y % 16777216).testBit k then φ (basisP k) else 1 := by
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    have hb : basisP k = (false, 2 ^ k, 0) := by simp [basisP, hk]
    rw [hb, show (16777216 : Nat) = 2 ^ 24 from rfl, Nat.testBit_mod_two_pow]
    simp [show k < 24 by omega]
  have h2 : ((List.range 12).map fun k =>
        if (y / 2 ^ 12).testBit k then φ (false, 0, 2 ^ k) else 1) =
      ((List.range 12).map (12 + ·)).map
        fun k => if (y % 16777216).testBit k then φ (basisP k) else 1 := by
    rw [List.map_map]
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    have hb : basisP (12 + k) = (false, 0, 2 ^ k) := by
      simp [basisP, show ¬ 12 + k < 12 by omega]
    rw [Function.comp_apply, hb, show (16777216 : Nat) = 2 ^ 24 from rfl,
      Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    simp [show 12 + k < 24 by omega, Nat.add_comm k 12]
  rw [show (24 : Nat) = 12 + 12 from rfl, List.range_add, List.map_append, List.prod_append,
    ← h1, ← h2, ← hT, ← hD, ← mul_assoc, ← hφ, ← hφ, mul_split, ← hu]

theorem applyN_spec : ∀ n acc yb rb, φ (unpackP (applyN n acc yb rb)) =
    φ (unpackP acc) * ((List.range n).map fun k =>
      if yb.testBit k then φ (unpackP (rb / 2 ^ (25 * k) % 33554432)) else 1).prod
  | 0, acc, _, _ => by
    rw [List.range_zero, List.map_nil, List.prod_nil, mul_one]
    rfl
  | n + 1, acc, yb, rb => by
    have hstep : φ (unpackP (bif Nat.beq (yb % 2) 1 then mulP acc (rb % 33554432) else acc)) =
        φ (unpackP acc) * (if yb.testBit 0 then φ (unpackP (rb % 33554432)) else 1) := by
      rcases Nat.mod_two_eq_zero_or_one yb with h | h
      · have h0 : yb.testBit 0 = false := by simp [Nat.testBit_zero, h]
        rw [h, h0]
        simp
      · have h0 : yb.testBit 0 = true := by simp [Nat.testBit_zero, h]
        rw [h, h0, show Nat.beq 1 1 = true from rfl, Bool.cond_true,
          ite_eq_left_of_eq_true _ _ (eq_self true), unpackP_mulP, hφ]
    have hl : ((List.range n).map fun k =>
          if (yb / 2).testBit k then φ (unpackP (rb / 33554432 / 2 ^ (25 * k) % 33554432))
          else 1) =
        (List.range n).map ((fun k =>
          if yb.testBit k then φ (unpackP (rb / 2 ^ (25 * k) % 33554432)) else 1) ∘ Nat.succ) := by
      apply List.map_congr_left
      intro k _
      rw [Function.comp_apply, Nat.testBit_succ, Nat.div_div_eq_div_mul,
        show (33554432 : Nat) * 2 ^ (25 * k) = 2 ^ (25 * Nat.succ k) by
          rw [Nat.succ_eq_add_one, Nat.mul_succ, Nat.pow_add, Nat.mul_comm]]
    rw [applyN_succ, applyN_spec n, hstep, hl, List.range_succ_eq_map, List.map_cons,
      List.prod_cons, List.map_map, mul_assoc, Nat.mul_zero, Nat.pow_zero, Nat.div_one]

end Hom

theorem applyN_lt : ∀ n {acc : Nat}, acc < 2 ^ 25 → ∀ yb rb, applyN n acc yb rb < 2 ^ 25
  | 0, _, h, _, _ => h
  | n + 1, acc, h, yb, rb => by
    rw [applyN_succ]
    refine applyN_lt n ?_ (yb / 2) (rb / 33554432)
    cases Nat.beq (yb % 2) 1
    · exact h
    · exact mulP_lt h (Nat.mod_lt _ (by decide))

end CFSG.KC.WordRelK
