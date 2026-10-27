module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Local
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
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.EvenSporadicStandard.J4Std

open Subgroup

variable {J G : Type} [Group J] [Group G] (ι : J →* G)

theorem mem_Hloc_map (hι : Function.Injective ι) (U : Subgroup J) {g : G} :
    g ∈ Hloc ι.range (U.map ι) ↔ ∃ j ∈ Hloc (⊤ : Subgroup J) U, ι j = g := by
  rw [mem_Hloc]
  constructor
  · rintro ⟨⟨j, rfl⟩, h⟩
    refine ⟨j, mem_Hloc.2 ⟨mem_top j, fun x => ?_⟩, rfl⟩
    have h1 := h (ι x)
    have e : ι j * ι x * (ι j)⁻¹ = ι (j * x * j⁻¹) := by simp
    rw [e, mem_map_iff_mem hι, mem_map_iff_mem hι] at h1
    exact h1
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨-, hj2⟩ := mem_Hloc.1 hj
    refine ⟨⟨j, rfl⟩, fun u' => ?_⟩
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨j * x * j⁻¹, (hj2 x).1 hx, by simp⟩
    · rintro ⟨x₀, hx₀, hx₀e⟩
      have hu : u' = ι (j⁻¹ * x₀ * j) := by
        have : u' = (ι j)⁻¹ * (ι j * u' * (ι j)⁻¹) * ι j := by group
        rw [this, ← hx₀e]; simp
      refine ⟨j⁻¹ * x₀ * j, ?_, hu.symm⟩
      have h3 := (hj2 (j⁻¹ * x₀ * j)).2
      have e : j * (j⁻¹ * x₀ * j) * j⁻¹ = x₀ := by group
      rw [e] at h3
      exact h3 hx₀

theorem Hloc_map (hι : Function.Injective ι) (U : Subgroup J) :
    Hloc ι.range (U.map ι) = (Hloc (⊤ : Subgroup J) U).map ι := by
  ext g
  rw [mem_Hloc_map ι hι, mem_map]

theorem mem_hOrbit_map (hι : Function.Injective ι) (U : Subgroup J) (a : J) {g : G} :
    g ∈ hOrbit ι.range (U.map ι) (ι a) ↔ ∃ u ∈ hOrbit (⊤ : Subgroup J) U a, ι u = g := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨j, hj, rfl⟩ := (mem_Hloc_map ι hι U).1 hh
    exact ⟨j * a * j⁻¹, ⟨j, hj, rfl⟩, by simp⟩
  · rintro ⟨u, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨ι j, (mem_Hloc_map ι hι U).2 ⟨j, hj, rfl⟩, by simp⟩

theorem hOrbit_map (hι : Function.Injective ι) (U : Subgroup J) (a : J) :
    hOrbit ι.range (U.map ι) (ι a) = ι '' hOrbit (⊤ : Subgroup J) U a := by
  ext g
  rw [mem_hOrbit_map ι hι, Set.mem_image]

end CFSG.EvenSporadicStandard.J4Std
