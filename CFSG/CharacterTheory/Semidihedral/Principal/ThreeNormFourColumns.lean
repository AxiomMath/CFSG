module

public import Mathlib.Algebra.BigOperators.ModEq
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

open scoped BigOperators Matrix

namespace CFSG.Semidihedral.Principal

namespace ThreeNormFour

theorem even_subsets_fin_three :
    ∀ s t : Finset (Fin 3), Even s.card → Even t.card → Even (s ∩ t).card →
      s = ∅ ∨ t = ∅ ∨ s = t := by
  decide

theorem even_subset_fin_three_ne_univ :
    ∀ s : Finset (Fin 3), Even s.card → ∃ c, c ∉ s := by
  decide

theorem entry_mul_modEq {a b : ℤ} (ha : a = -1 ∨ a = 0 ∨ a = 1) (hb : b = -1 ∨ b = 0 ∨ b = 1) :
    a * b ≡ (if a ≠ 0 ∧ b ≠ 0 then 1 else 0) [ZMOD 2] := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> decide

end ThreeNormFour

open ThreeNormFour

theorem three_norm_four_integral_columns_odd_gram_entry (k : ℕ) (_hk : 1 ≤ k)
    (U : Matrix (Fin k) (Fin 3) ℤ) (hU : Uᵀ * U = (4 : ℤ) • (1 : Matrix (Fin 3) (Fin 3) ℤ))
    (d : Fin k → ℝ) (hd : ∀ i, 0 < d i)
    (hUd : (Uᵀ.map (Int.cast : ℤ → ℝ)).mulVec d = 0) :
    (∃ i j, Odd ((U * Uᵀ) i j)) ∧
      ∃ i j, Odd (((4 : ℤ) • (1 : Matrix (Fin k) (Fin k) ℤ) - U * Uᵀ) i j) := by
  have hcol : ∀ j, ∑ i, U i j ^ 2 = 4 := by
    intro j
    have h := congrFun (congrFun hU j) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hdot : ∀ j, ∑ i, (U i j : ℝ) * d i = 0 := by
    intro j
    have h := congrFun hUd j
    simpa [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.transpose_apply] using h
  have hentry : ∀ i j, U i j = -1 ∨ U i j = 0 ∨ U i j = 1 := by
    intro i j
    have hle : U i j ^ 2 ≤ 4 := by
      rw [← hcol j]
      exact Finset.single_le_sum (f := fun i => U i j ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ i)
    have hne2 : U i j ^ 2 ≠ 4 := by
      intro h4
      have hrest : ∀ i' ∈ Finset.univ.erase i, U i' j = 0 := by
        have hsum := Finset.add_sum_erase Finset.univ (fun i => U i j ^ 2) (Finset.mem_univ i)
        rw [hcol j, h4] at hsum
        have hzero : ∑ i' ∈ Finset.univ.erase i, U i' j ^ 2 = 0 := by linarith
        intro i' hi'
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (U i j))).mp hzero i' hi'
        exact pow_eq_zero_iff (two_ne_zero) |>.mp this
      have hsum := hdot j
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i),
        Finset.sum_eq_zero (fun i' hi' => by rw [hrest i' hi', Int.cast_zero, zero_mul]),
        add_zero] at hsum
      have hU0 : (U i j : ℝ) ≠ 0 := by
        intro h0
        have : U i j = 0 := by exact_mod_cast h0
        rw [this] at h4
        norm_num at h4
      exact mul_ne_zero hU0 (hd i).ne' hsum
    have hb : -2 ≤ U i j ∧ U i j ≤ 2 := by
      constructor <;> nlinarith [sq_nonneg (U i j - 2), sq_nonneg (U i j + 2)]
    have h2 : U i j ≠ 2 := fun h => hne2 (by rw [h]; norm_num)
    have hm2 : U i j ≠ -2 := fun h => hne2 (by rw [h]; norm_num)
    omega
  let supp : Fin k → Finset (Fin 3) := fun i => Finset.univ.filter fun j => U i j ≠ 0
  have hgram : ∀ i i', (U * Uᵀ) i i' ≡ ((supp i ∩ supp i').card : ℤ) [ZMOD 2] := by
    intro i i'
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    have hcard : ((supp i ∩ supp i').card : ℤ) =
        ∑ j, (if U i j ≠ 0 ∧ U i' j ≠ 0 then 1 else 0) := by
      simp only [supp, ← Finset.filter_and]
      rw [Finset.card_filter]
      push_cast
      rfl
    rw [hcard]
    exact Int.ModEq.sum fun j _ => entry_mul_modEq (hentry i j) (hentry i' j)
  have hparity : ∀ n m : ℤ, n ≡ m [ZMOD 2] → (Odd n ↔ Odd m) := by
    intro n m h
    rw [Int.odd_iff, Int.odd_iff]
    rw [Int.ModEq] at h
    rw [h]
  have hodd : ∃ i j, Odd ((U * Uᵀ) i j) := by
    by_contra hnone
    push Not at hnone
    have heven : ∀ i i', Even ((supp i ∩ supp i').card) := by
      intro i i'
      have h := hnone i i'
      rw [Int.not_odd_iff_even] at h
      have h' := (hparity _ _ (hgram i i')).not
      rw [Int.not_odd_iff_even, Int.not_odd_iff_even] at h'
      have := h'.mp h
      exact_mod_cast this
    have hcard : ∀ i, Even (supp i).card := fun i => by
      simpa only [Finset.inter_self] using heven i i
    have hcolne : ∀ j, ∃ i, U i j ≠ 0 := by
      intro j
      by_contra hall
      push Not at hall
      have h := hcol j
      simp only [hall] at h
      norm_num at h
    obtain ⟨i₀, hi₀⟩ := hcolne 0
    have hne : supp i₀ ≠ ∅ := by
      intro h
      have : (0 : Fin 3) ∈ supp i₀ := by simp [supp, hi₀]
      rw [h] at this
      simp at this
    obtain ⟨c, hc⟩ := even_subset_fin_three_ne_univ (supp i₀) (hcard i₀)
    obtain ⟨i₁, hi₁⟩ := hcolne c
    have hc₁ : c ∈ supp i₁ := by simp [supp, hi₁]
    rcases even_subsets_fin_three (supp i₁) (supp i₀) (hcard i₁) (hcard i₀)
        (by simpa only [Finset.inter_comm] using heven i₀ i₁) with h | h | h
    · rw [h] at hc₁
      simp at hc₁
    · exact hne h
    · exact hc (h ▸ hc₁)
  refine ⟨hodd, ?_⟩
  obtain ⟨i, j, hij⟩ := hodd
  refine ⟨i, j, ?_⟩
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  have h4 : Even ((4 : ℤ) * (1 : Matrix (Fin k) (Fin k) ℤ) i j) :=
    ⟨2 * (1 : Matrix (Fin k) (Fin k) ℤ) i j, by ring⟩
  exact h4.sub_odd hij

end CFSG.Semidihedral.Principal
