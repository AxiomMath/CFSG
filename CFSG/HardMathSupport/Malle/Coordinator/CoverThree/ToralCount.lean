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
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThree

theorem exists_notMem_eq_of_hom {P : Type*} [Group P] [Finite P] {F : Type*} [Field F] [Finite F]
    (χ ψ : P →* F) (hcube : ∀ x, χ x ^ 3 = ψ x ^ 3) (hP : Nat.card P = 27) (Z : Subgroup P)
    (hZ : Nat.card Z = 3) : ∃ x : P, x ∉ Z ∧ χ x = ψ x := by
  classical
  let ρ : P →* Fˣ := χ.toHomUnits / ψ.toHomUnits
  have hρ : ∀ x, ρ x = 1 → χ x = ψ x := by
    intro x hx
    have h1 : ((χ.toHomUnits x : Fˣ) : F) = (ψ.toHomUnits x : Fˣ) := by
      have : χ.toHomUnits x / ψ.toHomUnits x = 1 := hx
      rw [div_eq_one] at this
      rw [this]
    simpa using h1
  have hrange : Nat.card ρ.range ≤ 3 := by
    have hle : ρ.range ≤ rootsOfUnity 3 F := by
      rintro _ ⟨x, rfl⟩
      rw [mem_rootsOfUnity]
      have hx : (χ.toHomUnits x) ^ 3 = (ψ.toHomUnits x) ^ 3 := Units.ext (hcube x)
      show (χ.toHomUnits x / ψ.toHomUnits x) ^ 3 = 1
      rw [div_pow, hx, div_self']
    exact (Subgroup.card_le_of_le hle).trans (card_rootsOfUnity F 3)
  have hidx : ρ.ker.index = Nat.card ρ.range := Subgroup.index_ker ρ
  have hker9 : 9 ≤ Nat.card ρ.ker := by
    have h := ρ.ker.card_mul_index
    rw [hP, hidx] at h
    have hpos : 0 < Nat.card ρ.range := Nat.card_pos
    by_contra hlt
    push Not at hlt
    nlinarith
  by_contra hcon
  push Not at hcon
  have hsub : ρ.ker ≤ Z := fun x hx => by
    by_contra hnx
    exact hcon x hnx (hρ x hx)
  have := Subgroup.card_le_of_le hsub
  omega

end CFSG.HardMathSupport.Malle.Coordinator.CoverThree
