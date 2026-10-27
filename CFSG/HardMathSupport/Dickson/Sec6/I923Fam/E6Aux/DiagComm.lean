module

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

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open Subgroup

theorem diag_mem_commutator {G M Q : Type*} [Group G] [CommGroup M] [Finite M] [CommGroup Q]
    (D : M →* G) (r : M →* M) (t : G) (ht : ∀ b, t * D b * t⁻¹ = D (r b))
    (Im : Subgroup M) (hIm : Im.index ∣ 3) (hImC : ∀ b ∈ Im, D b ∈ commutator G)
    (κ : M →* Q) (hQ : ∀ x : Q, x ^ 3 = 1) (hκIm : ∀ b ∈ Im, κ b = 1)
    (hκr : ∀ b, κ (r b * b) = 1) (hκ1 : (∀ b, κ b = 1) → ¬ 3 ∣ Nat.card M) :
    ∀ b, D b ∈ commutator G := by
  classical
  set T : Subgroup M := (commutator G).comap D with hT
  have hImT : Im ≤ T := fun b hb => hImC b hb
  have hTtop : T = ⊤ := by
    by_contra hne
    have hTidx : T.index ∣ 3 := (Subgroup.index_dvd_of_le hImT).trans hIm
    have hT1 : T.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.1 h)
    have hT3 : T.index = 3 := (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hTidx).resolve_left hT1
    have hI3 : Im.index = 3 := by
      have h1 : T.index ∣ Im.index := Subgroup.index_dvd_of_le hImT
      rw [hT3] at h1
      exact Nat.dvd_antisymm hIm h1
    have hIT : Im = T := by
      have h1 := Subgroup.relIndex_mul_index hImT
      rw [hT3, hI3] at h1
      have hrel : Im.relIndex T = 1 := by omega
      exact le_antisymm hImT (Subgroup.relIndex_eq_one.1 hrel)
    have hall : ∀ b, κ b = 1 := by
      intro b
      have hcomm : t * D b * t⁻¹ * (D b)⁻¹ ∈ commutator G := by
        rw [_root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (mem_top _) (mem_top _)
      rw [ht b] at hcomm
      have hmem : r b * b⁻¹ ∈ T := by
        show D (r b * b⁻¹) ∈ commutator G
        rwa [map_mul, map_inv]
      rw [← hIT] at hmem
      have h1 : κ (r b * b⁻¹) = 1 := hκIm _ hmem
      rw [map_mul, map_inv] at h1
      have h2 := hκr b
      rw [map_mul] at h2
      have h3 : κ (r b) = κ b := mul_inv_eq_one.1 h1
      rw [h3] at h2
      have h4 := hQ (κ b)
      calc κ b = κ b * (κ b * κ b) := by rw [h2, mul_one]
        _ = κ b ^ 3 := by rw [pow_succ, pow_two, mul_assoc]
        _ = 1 := h4
    exact hκ1 hall (hI3 ▸ Subgroup.index_dvd_card Im)
  intro b
  have : b ∈ T := hTtop ▸ mem_top b
  exact this

end CFSG.HardMathSupport.Dickson.Sec6.I923
