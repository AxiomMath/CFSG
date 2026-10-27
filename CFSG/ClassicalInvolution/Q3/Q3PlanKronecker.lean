module

public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.ClassicalInvolution.Q3

open Polynomial

section Eval

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

noncomputable def evalAt (c : k) (h : Polynomial (Module.End k V)) : Module.End k V :=
  h.eval₂ (RingHom.id _) (algebraMap k (Module.End k V) c)

theorem commute_algebraMap_evalAt (c : k) (a : Module.End k V) :
    Commute a (algebraMap k (Module.End k V) c) :=
  (Algebra.commutes c a).symm

theorem evalAt_add (c : k) (h h' : Polynomial (Module.End k V)) :
    evalAt c (h + h') = evalAt c h + evalAt c h' :=
  Polynomial.eval₂_add _ _

theorem evalAt_sub (c : k) (h h' : Polynomial (Module.End k V)) :
    evalAt c (h - h') = evalAt c h - evalAt c h' :=
  Polynomial.eval₂_sub _

theorem evalAt_mul (c : k) (h h' : Polynomial (Module.End k V)) :
    evalAt c (h * h') = evalAt c h * evalAt c h' :=
  Polynomial.eval₂_mul_noncomm _ _ fun _ => commute_algebraMap_evalAt c _

theorem evalAt_C (c : k) (a : Module.End k V) : evalAt c (C a) = a := by
  simp [evalAt]

theorem evalAt_X_pow (c : k) (n : ℕ) :
    evalAt c ((X : Polynomial (Module.End k V)) ^ n) = algebraMap k (Module.End k V) (c ^ n) := by
  simp [evalAt, map_pow]

theorem evalAt_X_pow_mul_C (c : k) (n : ℕ) (a : Module.End k V) :
    evalAt c ((X : Polynomial (Module.End k V)) ^ n * C a) = c ^ n • a := by
  rw [evalAt_mul, evalAt_X_pow, evalAt_C, Algebra.smul_def]

theorem evalAt_finset_sum (c : k) {ι : Type*} (s : Finset ι) (f : ι → Polynomial (Module.End k V)) :
    evalAt c (∑ i ∈ s, f i) = ∑ i ∈ s, evalAt c (f i) :=
  Polynomial.eval₂_finsetSum _ _ _ _

theorem eq_zero_of_evalAt_eq_zero (S : Finset k) (h : Polynomial (Module.End k V))
    (hdeg : h.natDegree < S.card) (h0 : ∀ c ∈ S, evalAt c h = 0) : h = 0 := by
  have hco : ∀ i v (φ : Module.Dual k V), φ ((h.coeff i) v) = 0 := by
    intro i v φ
    set Q : k[X] := ∑ j ∈ Finset.range (h.natDegree + 1), C (φ ((h.coeff j) v)) * X ^ j with hQ
    have hev : ∀ c, Q.eval c = φ ((evalAt c h) v) := by
      intro c
      rw [hQ, Polynomial.eval_finsetSum, evalAt, Polynomial.eval₂_eq_sum_range]
      simp only [LinearMap.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        RingHom.id_apply, Module.End.mul_apply, ← map_pow, Module.algebraMap_end_apply,
        map_smul, map_smul, smul_eq_mul, mul_comm]
    have hQdeg : Q.natDegree < S.card := by
      refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_) hdeg
      exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    have hQ0 : Q = 0 :=
      Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Q S
        (fun c hc => by rw [hev, h0 c hc]; simp) hQdeg
    by_cases hi : i ≤ h.natDegree
    · have hc := congrArg (fun p : k[X] => p.coeff i) hQ0
      simp only [hQ, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_zero] at hc
      rw [Finset.sum_eq_single i] at hc
      · simpa using hc
      · intro j _ hji
        simp [Ne.symm hji]
      · intro hi'
        exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)) hi'
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hi)]
      simp
  refine Polynomial.ext fun i => ?_
  rw [Polynomial.coeff_zero]
  refine LinearMap.ext fun v => ?_
  exact (Module.forall_dual_apply_eq_zero_iff k _).mp (fun φ => hco i v φ)

end Eval

section Window

variable {A : Type*} [Semiring A]

theorem coeff_X_pow_mul_window (m N i : ℕ) (R : Polynomial A) (hR : R.natDegree < N) (m' : ℕ)
    (hm' : m' ≠ m) (hi : i < N) :
    (X ^ (m' * N) * R).coeff (m * N + i) = 0 := by
  rw [Polynomial.coeff_X_pow_mul']
  split_ifs with h
  · apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rcases lt_or_gt_of_ne hm' with hlt | hgt
    · have h1 : m' * N + N ≤ m * N := by
        have := Nat.mul_le_mul_right N (Nat.succ_le_of_lt hlt)
        rwa [Nat.succ_mul] at this
      generalize m' * N = a at *
      generalize m * N = b at *
      omega
    · exfalso
      have h2 : m * N + N ≤ m' * N := by
        have := Nat.mul_le_mul_right N (Nat.succ_le_of_lt hgt)
        rwa [Nat.succ_mul] at this
      generalize m' * N = a at *
      generalize m * N = b at *
      omega
  · rfl

theorem window_eq_zero (N : ℕ) (R : ℕ → Polynomial A) (hR : ∀ m, (R m).natDegree < N)
    (h : ∑ m ∈ Finset.range 4, X ^ (m * N) * R m = 0) : ∀ m < 4, R m = 0 := by
  intro m hm
  refine Polynomial.ext fun i => ?_
  rw [Polynomial.coeff_zero]
  by_cases hi : i < N
  · have hc := congrArg (fun p : Polynomial A => p.coeff (m * N + i)) h
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_zero] at hc
    rw [Finset.sum_eq_single m] at hc
    · rw [Polynomial.coeff_X_pow_mul'] at hc
      split_ifs at hc with hle
      · rwa [Nat.add_sub_cancel_left] at hc
      · exact absurd (Nat.le_add_right _ _) hle
    · intro m' _ hm'
      exact coeff_X_pow_mul_window m N i (R m') (hR m') m' hm' hi
    · intro hm'
      exact absurd (Finset.mem_range.mpr hm) hm'
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hR m) (not_lt.mp hi))

end Window

section Product

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

noncomputable def factorPoly (q : ℕ) (P : ℕ → ℕ → Module.End k V) (j : ℕ) :
    Polynomial (Module.End k V) :=
  ∑ m ∈ Finset.range 4, X ^ (m * q ^ j) * C (P j m)

noncomputable def prodPoly (q : ℕ) (P : ℕ → ℕ → Module.End k V) (d : ℕ) :
    Polynomial (Module.End k V) :=
  ((List.range d).map (factorPoly q P)).prod

theorem prodPoly_succ (q : ℕ) (P : ℕ → ℕ → Module.End k V) (d : ℕ) :
    prodPoly q P (d + 1) = prodPoly q P d * factorPoly q P d := by
  simp [prodPoly, List.range_succ]

theorem prodPoly_zero (q : ℕ) (P : ℕ → ℕ → Module.End k V) : prodPoly q P 0 = 1 := by
  simp [prodPoly]

theorem natDegree_factorPoly_le (q : ℕ) (P : ℕ → ℕ → Module.End k V) (j : ℕ) :
    (factorPoly q P j).natDegree ≤ 3 * q ^ j := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  have hm3 : m ≤ 3 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  calc (X ^ (m * q ^ j) * C (P j m) : Polynomial (Module.End k V)).natDegree
      ≤ (X ^ (m * q ^ j) : Polynomial (Module.End k V)).natDegree + (C (P j m)).natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ 3 * q ^ j := by
        rw [Polynomial.natDegree_C, add_zero]
        exact (Polynomial.natDegree_X_pow_le _).trans (Nat.mul_le_mul_right _ hm3)

theorem natDegree_prodPoly_le (q : ℕ) (hq : 4 ≤ q) (P : ℕ → ℕ → Module.End k V) (d : ℕ) :
    (prodPoly q P d).natDegree + 1 ≤ q ^ d := by
  induction d with
  | zero => simp [prodPoly_zero]
  | succ d ih =>
    rw [prodPoly_succ]
    have h1 := Polynomial.natDegree_mul_le (p := prodPoly q P d) (q := factorPoly q P d)
    have h2 := natDegree_factorPoly_le q P d
    have h3 : 4 * q ^ d ≤ q ^ (d + 1) := by
      calc 4 * q ^ d ≤ q * q ^ d := Nat.mul_le_mul_right _ hq
        _ = q ^ (d + 1) := by ring
    omega

theorem coeff_zero_prodPoly (q : ℕ) (hq : 1 ≤ q) (P : ℕ → ℕ → Module.End k V)
    (hP : ∀ j, P j 0 = 1) (d : ℕ) : (prodPoly q P d).coeff 0 = 1 := by
  induction d with
  | zero => simp [prodPoly_zero]
  | succ d ih =>
    rw [prodPoly_succ, Polynomial.mul_coeff_zero, ih, one_mul, factorPoly,
      Polynomial.finsetSum_coeff, Finset.sum_eq_single 0]
    · simp [hP]
    · intro m _ hm
      have hpos : 0 < m * q ^ d := Nat.mul_pos (Nat.pos_of_ne_zero hm) (pow_pos (by omega) d)
      rw [Polynomial.coeff_X_pow_mul']
      split_ifs with hle
      · omega
      · rfl
    · intro h0
      exact absurd (Finset.mem_range.mpr (by norm_num)) h0

theorem mul_X_pow_mul_comm (a b : Polynomial (Module.End k V)) (n : ℕ) :
    a * (X ^ n * b) = X ^ n * (a * b) := by
  rw [← mul_assoc, ← Polynomial.X_pow_mul, mul_assoc]

theorem prodPoly_succ_eq_sum (q : ℕ) (P : ℕ → ℕ → Module.End k V) (d : ℕ) :
    prodPoly q P (d + 1) =
      ∑ m ∈ Finset.range 4, X ^ (m * q ^ d) * (prodPoly q P d * C (P d m)) := by
  rw [prodPoly_succ, factorPoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_X_pow_mul_comm]

theorem natDegree_comm_le (g : Module.End k V) (p : Polynomial (Module.End k V)) :
    (C g * p - p * C g).natDegree ≤ p.natDegree :=
  (Polynomial.natDegree_sub_le _ _).trans
    (max_le (Polynomial.natDegree_C_mul_le _ _) (Polynomial.natDegree_mul_C_le _ _))

theorem commute_of_commute_prodPoly (q : ℕ) (hq : 4 ≤ q) (P : ℕ → ℕ → Module.End k V)
    (hP : ∀ j, P j 0 = 1) (g : Module.End k V) :
    ∀ d, C g * prodPoly q P d = prodPoly q P d * C g →
      ∀ j < d, ∀ m < 4, g * P j m = P j m * g := by
  intro d
  induction d with
  | zero => intro _ j hj; omega
  | succ d ih =>
    intro h j hj m hm
    have hdeg : (prodPoly q P d).natDegree < q ^ d := by
      have := natDegree_prodPoly_le q hq P d
      omega
    have hsum : ∑ m' ∈ Finset.range 4, X ^ (m' * q ^ d) *
        (C g * (prodPoly q P d * C (P d m')) - (prodPoly q P d * C (P d m')) * C g) = 0 := by
      have e := sub_eq_zero.mpr h
      rw [prodPoly_succ_eq_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib] at e
      rw [← e]
      refine Finset.sum_congr rfl fun m' _ => ?_
      rw [mul_sub, mul_X_pow_mul_comm, mul_assoc, mul_assoc]
      simp only [mul_assoc]
    have hRdeg : ∀ m', (C g * (prodPoly q P d * C (P d m')) -
        (prodPoly q P d * C (P d m')) * C g).natDegree < q ^ d := by
      intro m'
      exact lt_of_le_of_lt ((natDegree_comm_le g _).trans (Polynomial.natDegree_mul_C_le _ _)) hdeg
    have hw := window_eq_zero (q ^ d) _ hRdeg hsum
    have hw' : ∀ m' < 4, C g * (prodPoly q P d * C (P d m')) =
        (prodPoly q P d * C (P d m')) * C g := fun m' hm' => sub_eq_zero.mp (hw m' hm')
    have hW0 : C g * prodPoly q P d = prodPoly q P d * C g := by
      have := hw' 0 (by norm_num)
      rwa [hP d, C_1, mul_one] at this
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjd | hjd
    · exact ih hW0 j hjd m hm
    · rw [hjd]
      have h1 := hw' m hm
      have h2 : prodPoly q P d * (C g * C (P d m) - C (P d m) * C g) = 0 := by
        rw [mul_sub, ← mul_assoc, ← hW0, mul_assoc, ← mul_assoc, ← mul_assoc, ← h1]
        simp [mul_assoc]
      have h3 := congrArg (fun p => p.coeff 0) h2
      simp only [Polynomial.mul_coeff_zero, coeff_zero_prodPoly q (by omega) P hP d, one_mul,
        Polynomial.coeff_zero, ← C_mul, ← C_sub, Polynomial.coeff_C_zero] at h3
      exact sub_eq_zero.mp h3

theorem commute_of_commute_evalAt_prodPoly (q : ℕ) (hq : 4 ≤ q) (P : ℕ → ℕ → Module.End k V)
    (hP : ∀ j, P j 0 = 1) (g : Module.End k V) (d : ℕ) (S : Finset k) (hS : q ^ d ≤ S.card)
    (h : ∀ c ∈ S, g * evalAt c (prodPoly q P d) = evalAt c (prodPoly q P d) * g) :
    ∀ j < d, ∀ m < 4, g * P j m = P j m * g := by
  refine commute_of_commute_prodPoly q hq P hP g d ?_
  have hz : C g * prodPoly q P d - prodPoly q P d * C g = 0 := by
    refine eq_zero_of_evalAt_eq_zero S _ ?_ ?_
    · have := natDegree_prodPoly_le q hq P d
      exact lt_of_le_of_lt (natDegree_comm_le g _) (by omega)
    · intro c hc
      rw [evalAt_sub, evalAt_mul, evalAt_mul, evalAt_C]
      exact sub_eq_zero.mpr (h c hc)
  exact sub_eq_zero.mp hz

theorem evalAt_prodPoly (q : ℕ) (P : ℕ → ℕ → Module.End k V) (c : k) (d : ℕ) :
    evalAt c (prodPoly q P d) = ((List.range d).map fun j => evalAt c (factorPoly q P j)).prod := by
  induction d with
  | zero => simp [prodPoly_zero, evalAt]
  | succ d ih =>
    rw [prodPoly_succ, evalAt_mul, ih, List.range_succ, List.map_append, List.prod_append]
    simp

theorem evalAt_factorPoly (q : ℕ) (P : ℕ → ℕ → Module.End k V) (c : k) (j : ℕ) :
    evalAt c (factorPoly q P j) = ∑ m ∈ Finset.range 4, (c ^ q ^ j) ^ m • P j m := by
  rw [factorPoly, evalAt_finset_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [evalAt_X_pow_mul_C, pow_mul']

theorem commute_unit_family (q : ℕ) (hq : 4 ≤ q) (d : ℕ) (S : Finset k) (hS : q ^ d ≤ S.card)
    (u : ℕ → k → (Module.End k V)ˣ) (P : ℕ → ℕ → Module.End k V) (hP0 : ∀ j, P j 0 = 1)
    (hu : ∀ j s, ((u j s : (Module.End k V)ˣ) : Module.End k V) =
      ∑ m ∈ Finset.range 4, s ^ m • P j m) (g : (Module.End k V)ˣ)
    (hg : ∀ c ∈ S, g * ((List.range d).map fun j => u j (c ^ q ^ j)).prod =
      ((List.range d).map fun j => u j (c ^ q ^ j)).prod * g) :
    ∀ j < d, ∀ s : k, g * u j s = u j s * g := by
  have hcoe : ∀ c : k, ((((List.range d).map fun j => u j (c ^ q ^ j)).prod :
      (Module.End k V)ˣ) : Module.End k V) = evalAt c (prodPoly q P d) := by
    intro c
    rw [evalAt_prodPoly, ← Units.coeHom_apply, map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    rw [Function.comp_apply, Units.coeHom_apply, hu, evalAt_factorPoly]
  have hP := commute_of_commute_evalAt_prodPoly q hq P hP0 (g : Module.End k V) d S hS
    (fun c hc => by
      rw [← hcoe c]
      exact congrArg Units.val (hg c hc))
  intro j hj s
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hu, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mul_smul_comm, smul_mul_assoc, hP j hj m (Finset.mem_range.mp hm)]

end Product

end CFSG.ClassicalInvolution.Q3
