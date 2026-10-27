module

public import CFSG.Sporadic.HNSchreier.OrbitCheckInputs
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KS.SporSch.HNXP

open CFSG.Sporadic.Th.Native CFSG.Sporadic.HNSchreier.Native

theorem bfs_strict {n : Nat} {pp : Nat → Nat}
    (hmono : ∀ i, 0 < i → i < n → pp (i - 1) < pp i ∧ pp i ≤ 2 * i) :
    ∀ b a, a < b → b < n → pp a < pp b := by
  intro b
  induction b with
  | zero => intro a h; omega
  | succ b ih =>
    intro a hab hb
    have h1 := (hmono (b + 1) (by omega) hb).1
    simp only [Nat.add_sub_cancel] at h1
    rcases Nat.lt_succ_iff_lt_or_eq.mp hab with h | h
    · exact Nat.lt_trans (ih a h (by omega)) h1
    · subst h; exact h1

theorem bfs_mono_le {n : Nat} {pp : Nat → Nat}
    (hmono : ∀ i, 0 < i → i < n → pp (i - 1) < pp i ∧ pp i ≤ 2 * i)
    {a b : Nat} (hab : a ≤ b) (hb : b < n) : pp a ≤ pp b := by
  rcases Nat.lt_or_eq_of_le hab with h | h
  · exact Nat.le_of_lt (bfs_strict hmono b a h hb)
  · subst h; exact Nat.le_refl _

def bfsQ (n : Nat) (pp : Nat → Nat) (p m : Nat) : Prop :=
  m ≤ n ∧ ∀ t < n, (t < m ↔ pp t ≤ p)

theorem bfs_half {n : Nat} {pp : Nat → Nat}
    (hmono : ∀ i, 0 < i → i < n → pp (i - 1) < pp i ∧ pp i ≤ 2 * i)
    {p m v : Nat} (hQ : bfsQ n pp p m) (hv : v < n) (hpv : pp v ≤ p + 1)
    (huniq : ∀ t < n, pp t = p + 1 → v = t) :
    v ≤ m ∧ bfsQ n pp (p + 1) (max m (v + 1)) := by
  obtain ⟨hmn, hQ⟩ := hQ
  have hvm : v ≤ m := by
    refine Nat.le_of_not_lt fun hlt => ?_
    have hm : m < n := by omega
    have h1 := bfs_strict hmono v m hlt hv
    have h2 : ¬ pp m ≤ p := fun h => Nat.lt_irrefl m ((hQ m hm).mpr h)
    have := huniq m hm (by omega)
    omega
  refine ⟨hvm, by omega, fun t ht => ?_⟩
  have hQt := hQ t ht
  constructor
  · intro h
    rcases Nat.lt_or_ge t m with h' | h'
    · have := hQt.mp h'; omega
    · have hle : t ≤ v := by omega
      have := bfs_mono_le hmono hle hv
      omega
  · intro h
    rcases Nat.lt_or_eq_of_le h with h' | h'
    · have := hQt.mpr (by omega); omega
    · have := huniq t ht h'; omega

theorem bfs_step {n : Nat} {α β : Table} {pp : Nat → Nat}
    (hpp0 : pp 0 = 0) (hmono : ∀ i, 0 < i → i < n → pp (i - 1) < pp i ∧ pp i ≤ 2 * i)
    (hlt : ∀ i < n, ap α i < n ∧ ap β i < n)
    (hedge : ∀ i < n, pp (ap α i) ≤ 2 * i + 1 ∧ pp (ap β i) ≤ 2 * i + 2)
    (hfirst : ∀ t, 0 < t → t < n → ∃ i < n,
      (pp t = 2 * i + 1 ∧ ap α i = t) ∨ (pp t = 2 * i + 2 ∧ ap β i = t))
    {i m : Nat} (hi : i < n) (hQ : bfsQ n pp (2 * i) m) :
    ∃ m', ordStepT α β (true, m) i = (true, m') ∧ bfsQ n pp (2 * (i + 1)) m' := by
  have hpi : pp i ≤ 2 * i := by
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; omega
    · exact (hmono i h hi).2
  have him : i < m := (hQ.2 i hi).mpr hpi
  obtain ⟨hva, hvb⟩ := hlt i hi
  obtain ⟨hea, heb⟩ := hedge i hi
  have hua : ∀ t < n, pp t = 2 * i + 1 → ap α i = t := by
    intro t ht hpt
    have ht0 : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · subst h; omega
      · exact h
    obtain ⟨i', -, h | h⟩ := hfirst t ht0 ht
    · have : i' = i := by omega
      subst this; exact h.2
    · omega
  obtain ⟨hA, hQ1⟩ := bfs_half hmono hQ hva hea hua
  have hub : ∀ t < n, pp t = 2 * i + 1 + 1 → ap β i = t := by
    intro t ht hpt
    have ht0 : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · subst h; omega
      · exact h
    obtain ⟨i', -, h | h⟩ := hfirst t ht0 ht
    · omega
    · have : i' = i := by omega
      subst this; exact h.2
  obtain ⟨hB, hQ2⟩ := bfs_half hmono hQ1 hvb heb hub
  refine ⟨_, ?_, by rw [show 2 * (i + 1) = 2 * i + 1 + 1 by omega]; exact hQ2⟩
  simp [ordStepT, him, hA, hB]

theorem bfs_fold {n : Nat} {α β : Table} {pp : Nat → Nat} (hn : 0 < n)
    (hpp0 : pp 0 = 0) (hmono : ∀ i, 0 < i → i < n → pp (i - 1) < pp i ∧ pp i ≤ 2 * i)
    (hlt : ∀ i < n, ap α i < n ∧ ap β i < n)
    (hedge : ∀ i < n, pp (ap α i) ≤ 2 * i + 1 ∧ pp (ap β i) ≤ 2 * i + 2)
    (hfirst : ∀ t, 0 < t → t < n → ∃ i < n,
      (pp t = 2 * i + 1 ∧ ap α i = t) ∨ (pp t = 2 * i + 2 ∧ ap β i = t)) :
    ∀ k, k ≤ n → ∃ m, (List.range k).foldl (ordStepT α β) (true, 1) = (true, m) ∧
      bfsQ n pp (2 * k) m := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨1, rfl, by omega, fun t ht => ?_⟩
    constructor
    · intro h; have : t = 0 := by omega
      subst this; omega
    · intro h
      rcases Nat.eq_zero_or_pos t with h' | h'
      · omega
      · have := bfs_strict hmono t 0 h' ht; omega
  | succ k ih =>
    intro hk
    obtain ⟨m, hm, hQ⟩ := ih (by omega)
    obtain ⟨m', hm', hQ'⟩ := bfs_step hpp0 hmono hlt hedge hfirst (by omega : k < n) hQ
    exact ⟨m', by rw [List.range_succ, List.foldl_append, hm]; simpa using hm', hQ'⟩

theorem bfsOrderOK_of {n : Nat} {α β : Table} {pp : Nat → Nat} (hn : 0 < n)
    (hpp0 : pp 0 = 0) (hmono : ∀ i, 0 < i → i < n → pp (i - 1) < pp i ∧ pp i ≤ 2 * i)
    (hlt : ∀ i < n, ap α i < n ∧ ap β i < n)
    (hedge : ∀ i < n, pp (ap α i) ≤ 2 * i + 1 ∧ pp (ap β i) ≤ 2 * i + 2)
    (hfirst : ∀ t, 0 < t → t < n → ∃ i < n,
      (pp t = 2 * i + 1 ∧ ap α i = t) ∨ (pp t = 2 * i + 2 ∧ ap β i = t)) :
    bfsOrderOK n α β = true := by
  obtain ⟨m, hm, hmn, hQ⟩ := bfs_fold hn hpp0 hmono hlt hedge hfirst n (Nat.le_refl n)
  have hlast : n - 1 < m := by
    refine (hQ (n - 1) (by omega)).mpr ?_
    rcases Nat.eq_zero_or_pos (n - 1) with h | h
    · rw [h, hpp0]; omega
    · have := (hmono (n - 1) h (by omega)).2; omega
  have : m = n := by omega
  subst this
  simp [bfsOrderOK, hm]

end CFSG.KS.SporSch.HNXP
