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
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
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

namespace CFSG.KC.Misc.RankOne

open scoped Matrix

theorem comp_self_eq_smul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : V →ₗ[K] V)
    (hf : Module.finrank K (LinearMap.range f) ≤ 1) : ∃ c : K, f ∘ₗ f = c • f := by
  obtain ⟨u, hu⟩ := (finrank_le_one_iff (K := K) (V := LinearMap.range f)).1 hf
  obtain ⟨c, hc⟩ := hu ⟨f u, LinearMap.mem_range_self f u⟩
  refine ⟨c, LinearMap.ext fun v => ?_⟩
  obtain ⟨d, hd⟩ := hu ⟨f v, LinearMap.mem_range_self f v⟩
  have hc' : c • (u : V) = f u := congrArg Subtype.val hc
  have hd' : d • (u : V) = f v := congrArg Subtype.val hd
  rw [LinearMap.comp_apply, LinearMap.smul_apply, ← hd', map_smul, ← hc']
  exact smul_comm d c (u : V)

theorem sq_eq_of_rank_le_one {K : Type*} [Field K] [Fintype K] (hK : Fintype.card K = 2)
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (h : (M - 1).rank ≤ 1) : M * M = 1 ∨ M * M = M := by
  obtain ⟨c, hc⟩ := comp_self_eq_smul (M - 1).mulVecLin h
  have hN : (M - 1) * (M - 1) = c • (M - 1) := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, map_smul]
    exact hc
  have two : (2 : K) = 0 := by
    have := FiniteField.cast_card_eq_zero K
    rwa [hK, Nat.cast_ofNat] at this
  have h2 : ∀ A : Matrix n n K, A + A = 0 := fun A => by
    rw [← two_smul K A, two, zero_smul]
  have key : M * M = (M - 1) * (M - 1) + (M + M) - 1 := by noncomm_ring
  have hneg : (-1 : Matrix n n K) = 1 := neg_eq_of_add_eq_zero_left (h2 1)
  by_cases hc0 : c = 0
  · left
    rw [key, hN, h2 M, hc0, zero_smul, add_zero, zero_sub, hneg]
  · right
    have hc1 : c = 1 := by
      have := FiniteField.pow_card_sub_one_eq_one c hc0
      rwa [hK, pow_one] at this
    rw [key, hN, h2 M, hc1, one_smul, add_zero, sub_sub, h2 1, sub_zero]

theorem rank_le_one_of_card_fix {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (hK : Fintype.card K = 2) (M : Matrix (Fin 4) (Fin 4) K)
    (h : 8 ≤ (Finset.univ.filter fun v : Fin 4 → K => M *ᵥ v = v).card) :
    (M - 1).rank ≤ 1 := by
  classical
  have hker : (Finset.univ.filter fun v : Fin 4 → K => M *ᵥ v = v).card
      = Fintype.card (LinearMap.ker (M - 1).mulVecLin) := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun v => by
      simp [LinearMap.mem_ker, Matrix.sub_mulVec, sub_eq_zero])
  have hcard := Module.card_eq_pow_finrank (K := K) (V := LinearMap.ker (M - 1).mulVecLin)
  rw [hK] at hcard
  have hk : 3 ≤ Module.finrank K (LinearMap.ker (M - 1).mulVecLin) := by
    by_contra! hlt
    have h4 : 2 ^ Module.finrank K (LinearMap.ker (M - 1).mulVecLin) ≤ 2 ^ 2 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hrn := LinearMap.finrank_range_add_finrank_ker (M - 1).mulVecLin
  rw [Module.finrank_fin_fun] at hrn
  change Module.finrank K (LinearMap.range (M - 1).mulVecLin) ≤ 1
  omega

end CFSG.KC.Misc.RankOne
