module

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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicRank

open Finset

theorem rank_le_nine {V G : Type*} [Fintype V] [DecidableEq V] [DecidableEq G]
    (hV : Fintype.card V = 3 ^ 7) (fix : G → Finset V) (O : Finset G)
    (h1 : O.card < 6560) (h2 : ∀ g ∈ O, (fix g).card ≤ 243)
    (h3a : (univ.filter fun v : V => 2186 ≤ (O.filter fun g => v ∈ fix g).card).card ≤ 26)
    (h3b : (univ.filter fun v : V => 728 ≤ (O.filter fun g => v ∈ fix g).card).card ≤ 80)
    (h4 : (univ.filter fun v : V => 242 ≤
      ((O.filter fun g => 243 ≤ (fix g).card).filter fun g => v ∈ fix g).card).card ≤ 242)
    (S : Finset G) (hSO : S ⊆ O) (B : Finset V) {a j : ℕ} (hB : B.card = 3 ^ a)
    (hS : S.card + 1 = 3 ^ j) (hfix : ∀ g ∈ S, B ⊆ fix g) : a + j ≤ 9 := by
  have hBle : 3 ^ a ≤ 3 ^ 7 := by
    rw [← hB, ← hV]
    exact Finset.card_le_univ B
  have ha7 : a ≤ 7 := (Nat.pow_le_pow_iff_right (by norm_num)).1 hBle
  have hSle : S.card ≤ O.card := Finset.card_le_card hSO
  have hj7 : j ≤ 7 := by
    by_contra hj
    have : 3 ^ 8 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  by_cases hSe : S = ∅
  · subst hSe
    have : 3 ^ j = 1 := by simpa using hS.symm
    have hj0 : j = 0 := by
      rcases Nat.pow_eq_one.mp this with h | h
      · omega
      · exact h
    omega
  obtain ⟨g0, hg0⟩ := Finset.nonempty_iff_ne_empty.mpr hSe
  have ha5 : a ≤ 5 := by
    have h' : 3 ^ a ≤ 243 := hB ▸ (Finset.card_le_card (hfix g0 hg0)).trans (h2 g0 (hSO hg0))
    by_contra ha
    have : 3 ^ 6 ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  by_cases hj4 : j ≤ 4
  · omega
  have hj5 : 5 ≤ j := by omega
  by_cases ha2 : a ≤ 2
  · omega
  have ha3 : 3 ≤ a := by omega
  have key : ∀ (bad : Finset V), bad.card < B.card → ∃ b ∈ B, b ∉ bad := fun bad hbad => by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact absurd (Finset.card_le_card (fun x hx => h x hx)) (not_le.2 hbad)
  have hSb : ∀ b ∈ B, S ⊆ O.filter fun g => b ∈ fix g := fun b hb g hg =>
    Finset.mem_filter.2 ⟨hSO hg, hfix g hg hb⟩
  have hSj : S.card + 1 = 3 ^ j := hS
  by_contra hcon
  have hj6 : 6 ≤ j ∨ 5 ≤ j := Or.inr hj5
  rcases (by omega : a = 3 ∨ a = 4 ∨ a = 5) with rfl | rfl | rfl
  ·
    have hj7' : j = 7 := by omega
    subst hj7'
    obtain ⟨b, hbB, hbb⟩ := key _ (by rw [hB]; omega : (univ.filter fun v : V => 2186 ≤
      (O.filter fun g => v ∈ fix g).card).card < B.card)
    have hb' : (O.filter fun g => b ∈ fix g).card < 2186 := by
      by_contra hc
      exact hbb (Finset.mem_filter.2 ⟨Finset.mem_univ _, not_lt.1 hc⟩)
    have := Finset.card_le_card (hSb b hbB)
    norm_num at hSj
    omega
  ·
    have h6 : 3 ^ 6 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨b, hbB, hbb⟩ := key _ (by rw [hB]; omega : (univ.filter fun v : V => 728 ≤
      (O.filter fun g => v ∈ fix g).card).card < B.card)
    have hb' : (O.filter fun g => b ∈ fix g).card < 728 := by
      by_contra hc
      exact hbb (Finset.mem_filter.2 ⟨Finset.mem_univ _, not_lt.1 hc⟩)
    have := Finset.card_le_card (hSb b hbB)
    norm_num at h6 hB
    omega
  ·
    have hSO5 : S ⊆ O.filter fun g => 243 ≤ (fix g).card := fun g hg =>
      Finset.mem_filter.2 ⟨hSO hg, by
        have := Finset.card_le_card (hfix g hg)
        rw [hB] at this
        norm_num at this
        exact this⟩
    obtain ⟨b, hbB, hbb⟩ := key _ (by rw [hB]; omega : (univ.filter fun v : V => 242 ≤
      ((O.filter fun g => 243 ≤ (fix g).card).filter fun g => v ∈ fix g).card).card < B.card)
    have hb' : ((O.filter fun g => 243 ≤ (fix g).card).filter fun g => b ∈ fix g).card < 242 := by
      by_contra hc
      exact hbb (Finset.mem_filter.2 ⟨Finset.mem_univ _, not_lt.1 hc⟩)
    have hsub : S ⊆ (O.filter fun g => 243 ≤ (fix g).card).filter fun g => b ∈ fix g :=
      fun g hg => Finset.mem_filter.2 ⟨hSO5 hg, hfix g hg hbB⟩
    have := Finset.card_le_card hsub
    have h5 : 3 ^ 5 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj5
    norm_num at h5
    omega

end CFSG.HardMathSupport.Timmesfeld.SporadicRank
