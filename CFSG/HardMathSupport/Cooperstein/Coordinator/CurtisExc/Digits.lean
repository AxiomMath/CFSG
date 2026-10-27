module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Colex
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

theorem geom_two_pow (x t : ℕ) (hx : 1 ≤ x) : (x - 1) * (∑ j ∈ Finset.range t, x ^ j) + 1 = x ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, mul_add, add_right_comm, ih, pow_succ]
    obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
    simp [Nat.add_sub_cancel]
    ring

theorem sum_two_pow_le (J : Finset ℕ) {n : ℕ} (hJ : ∀ i ∈ J, i < n) :
    ∑ i ∈ J, 2 ^ i ≤ 2 ^ n - 1 := by
  have h1 : ∑ i ∈ J, 2 ^ i ≤ ∑ i ∈ Finset.range n, 2 ^ i :=
    Finset.sum_le_sum_of_subset (fun i hi => Finset.mem_range.2 (hJ i hi))
  have h2 := geom_two_pow 2 n (by norm_num)
  have h3 : ∑ i ∈ Finset.range n, 2 ^ i + 1 = 2 ^ n := by simpa using h2
  omega

theorem bitIndices_add_two_pow_mul {g e x : ℕ} (he : e < 2 ^ g) :
    (e + 2 ^ g * x).bitIndices = e.bitIndices ++ x.bitIndices.map (· + g) := by
  have hsorted : List.SortedLT (e.bitIndices ++ x.bitIndices.map (· + g)) := by
    rw [List.sortedLT_iff_pairwise, List.pairwise_append]
    refine ⟨Nat.bitIndices_sorted.pairwise, ?_, ?_⟩
    · rw [List.pairwise_map]
      exact (Nat.bitIndices_sorted.pairwise).imp (by intro a b h; omega)
    · intro a ha b hb
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
      have h1 := Nat.two_pow_le_of_mem_bitIndices ha
      have : a < g := by
        by_contra hag
        have : 2 ^ g ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      omega
  have hsum : ((e.bitIndices ++ x.bitIndices.map (· + g)).map (fun i => 2 ^ i)).sum =
      e + 2 ^ g * x := by
    rw [List.map_append, List.sum_append, List.map_map, Nat.sum_map_two_pow_bitIndices]
    congr 1
    have : ((fun i => 2 ^ i) ∘ (· + g)) = fun i => 2 ^ g * 2 ^ i := by
      ext i; simp [pow_add, mul_comm]
    rw [this, List.sum_map_mul_left, Nat.sum_map_two_pow_bitIndices]
  rw [← hsum, Nat.bitIndices_sum_map_two_pow hsorted]

theorem length_bitIndices_rep {g e : ℕ} (he : e < 2 ^ g) (t : ℕ) :
    (∑ j ∈ Finset.range t, 2 ^ (g * j) * e).bitIndices.length = t * e.bitIndices.length := by
  induction t with
  | zero => simp
  | succ t ih =>
    have : ∑ j ∈ Finset.range (t + 1), 2 ^ (g * j) * e =
        e + 2 ^ g * ∑ j ∈ Finset.range t, 2 ^ (g * j) * e := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp only [mul_zero, pow_zero, one_mul]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mul_assoc, ← pow_add, mul_add, mul_one, add_comm g]
    rw [this, bitIndices_add_two_pow_mul he, List.length_append, List.length_map, ih]
    ring

theorem card_ge_of_periodic {n g : ℕ} (hg : 1 ≤ g) (hgn : g ∣ n) {J : Finset ℕ}
    (hJ : ∀ i ∈ J, i < n) (hne : J.Nonempty)
    (hper : (2 ^ n - 1) ∣ (2 ^ g - 1) * ∑ i ∈ J, 2 ^ i) : n / g ≤ J.card := by
  obtain ⟨t, rfl⟩ := hgn
  have ht : g * t / g = t := Nat.mul_div_cancel_left t hg
  rw [ht]
  set b := ∑ i ∈ J, 2 ^ i with hb
  have hb1 : 1 ≤ b := by
    obtain ⟨i, hi⟩ := hne
    exact le_trans (Nat.one_le_two_pow) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi)
  have hbn : b ≤ 2 ^ (g * t) - 1 := sum_two_pow_le J hJ
  set ĝ := ∑ j ∈ Finset.range t, (2 ^ g) ^ j with hĝ
  have hgeo : (2 ^ g - 1) * ĝ + 1 = 2 ^ (g * t) := by
    rw [hĝ, geom_two_pow (2 ^ g) t Nat.one_le_two_pow, pow_mul]
  have hpos : 0 < 2 ^ g - 1 := by
    have : 2 ^ 1 ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
    omega
  obtain ⟨e, he⟩ := hper
  have h2 : (2 ^ g - 1) * b = (2 ^ g - 1) * (ĝ * e) := by
    rw [he]
    have : 2 ^ (g * t) - 1 = (2 ^ g - 1) * ĝ := by omega
    rw [this]; ring
  have hbe : b = ĝ * e := Nat.eq_of_mul_eq_mul_left hpos h2
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · rw [h0, mul_zero] at hbe; omega
    · exact h0
  have hĝpos : 0 < ĝ := by
    rcases Nat.eq_zero_or_pos ĝ with h0 | h0
    · rw [h0, zero_mul] at hbe; omega
    · exact h0
  have he2 : e < 2 ^ g := by
    by_contra hcon
    push Not at hcon
    have : ĝ * 2 ^ g ≤ ĝ * e := Nat.mul_le_mul_left _ hcon
    have h3 : (2 ^ g - 1) * ĝ + 1 = 2 ^ (g * t) := hgeo
    have : ĝ * (2 ^ g - 1) + ĝ ≤ ĝ * e := by
      have : ĝ * 2 ^ g = ĝ * (2 ^ g - 1) + ĝ := by
        obtain ⟨y, hy⟩ : ∃ y, 2 ^ g = y + 1 := ⟨2 ^ g - 1, by omega⟩
        rw [hy]; simp; ring
      omega
    nlinarith
  have hrep : b = ∑ j ∈ Finset.range t, 2 ^ (g * j) * e := by
    rw [hbe, hĝ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← pow_mul]
  have hcard : J.card = b.bitIndices.length := by
    have h1 : b.bitIndices.toFinset = J := Finset.toFinset_bitIndices_sum_two_pow J
    conv_lhs => rw [← h1]
    exact List.toFinset_card_of_nodup Nat.bitIndices_nodup
  have hlen : 1 ≤ e.bitIndices.length := by
    by_contra h0
    have hnil : e.bitIndices = [] := List.length_eq_zero_iff.1 (by omega)
    have := Nat.sum_map_two_pow_bitIndices e
    rw [hnil] at this
    simp at this
    omega
  rw [hcard, hrep, length_bitIndices_rep he2]
  calc t = t * 1 := (mul_one t).symm
    _ ≤ t * e.bitIndices.length := Nat.mul_le_mul_left _ hlen

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
