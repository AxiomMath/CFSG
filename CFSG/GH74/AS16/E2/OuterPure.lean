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

namespace CFSG.GH74.AS16.E2

open Subgroup

@[expose] def InnerAt {G : Type*} [Group G] (L : Subgroup G) (x : G) : Prop :=
  ∃ l ∈ L, ∀ y ∈ L, x * y * x⁻¹ = l * y * l⁻¹

section Inner

variable {G : Type*} [Group G] {L : Subgroup G}

theorem InnerAt.of_mem {x : G} (hx : x ∈ L) : InnerAt L x := ⟨x, hx, fun _ _ => rfl⟩

theorem InnerAt.of_centralizer {x : G} (hx : x ∈ centralizer (L : Set G)) : InnerAt L x :=
  ⟨1, L.one_mem, fun y hy => by
    have := Subgroup.mem_centralizer_iff.1 hx y hy
    calc x * y * x⁻¹ = (y * x) * x⁻¹ := by rw [this]
      _ = 1 * y * 1⁻¹ := by group⟩

theorem InnerAt.mul {x y : G} (hx : InnerAt L x) (hy : InnerAt L y) : InnerAt L (x * y) := by
  obtain ⟨l₁, hl₁, h₁⟩ := hx
  obtain ⟨l₂, hl₂, h₂⟩ := hy
  refine ⟨l₁ * l₂, L.mul_mem hl₁ hl₂, fun z hz => ?_⟩
  have h2 := h₂ z hz
  have hmem : l₂ * z * l₂⁻¹ ∈ L := L.mul_mem (L.mul_mem hl₂ hz) (L.inv_mem hl₂)
  calc x * y * z * (x * y)⁻¹ = x * (y * z * y⁻¹) * x⁻¹ := by group
    _ = x * (l₂ * z * l₂⁻¹) * x⁻¹ := by rw [h2]
    _ = l₁ * (l₂ * z * l₂⁻¹) * l₁⁻¹ := h₁ _ hmem
    _ = l₁ * l₂ * z * (l₁ * l₂)⁻¹ := by group

theorem InnerAt.inv {x : G} (hx : InnerAt L x) : InnerAt L x⁻¹ := by
  obtain ⟨l, hl, h⟩ := hx
  refine ⟨l⁻¹, L.inv_mem hl, fun z hz => ?_⟩
  have hz' : l⁻¹ * z * l ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hl) hz) hl
  have h1 := h (l⁻¹ * z * l) hz'
  have h2 : x * (l⁻¹ * z * l) * x⁻¹ = z := by rw [h1]; group
  calc x⁻¹ * z * x⁻¹⁻¹ = x⁻¹ * (x * (l⁻¹ * z * l) * x⁻¹) * x := by rw [h2]; group
    _ = l⁻¹ * z * l := by group
    _ = l⁻¹ * z * l⁻¹⁻¹ := by group

@[expose] def innerSub (X L : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ X ∧ InnerAt L x}
  mul_mem' := fun ⟨hxX, hxi⟩ ⟨hyX, hyi⟩ => ⟨X.mul_mem hxX hyX, hxi.mul hyi⟩
  one_mem' := ⟨X.one_mem, InnerAt.of_mem L.one_mem⟩
  inv_mem' := fun ⟨hxX, hxi⟩ => ⟨X.inv_mem hxX, hxi.inv⟩

theorem innerSub_le {X L : Subgroup G} : innerSub X L ≤ X := fun _ hx => hx.1

theorem eq_mul_of_inv_mul_mem {R : Subgroup G} {v j : G}
    (hvL : v ∈ L) (hjD : j ∈ centralizer (L : Set G))
    (hRD : R ⊓ centralizer (L : Set G) = ⊥) (hr₀R : v * j ∈ R) {x : G} (hxR : x ∈ R)
    (hxD : v⁻¹ * x ∈ centralizer (L : Set G)) : x = v * j := by
  have hdc : ∀ y ∈ centralizer (L : Set G), v * y = y * v := fun y hy =>
    Subgroup.mem_centralizer_iff.1 hy v hvL
  have hmem : x * (v * j)⁻¹ ∈ R ⊓ centralizer (L : Set G) := by
    refine ⟨R.mul_mem hxR (R.inv_mem hr₀R), ?_⟩
    have e : x * (v * j)⁻¹ = (v⁻¹ * x) * j⁻¹ := by
      have h1 : v * (v⁻¹ * x) = (v⁻¹ * x) * v := hdc _ hxD
      have hjv : v * j⁻¹ = j⁻¹ * v := hdc _ ((centralizer (L : Set G)).inv_mem hjD)
      calc x * (v * j)⁻¹ = (v * (v⁻¹ * x)) * (j⁻¹ * v⁻¹) := by group
        _ = ((v⁻¹ * x) * v) * (j⁻¹ * v⁻¹) := by rw [h1]
        _ = (v⁻¹ * x) * (v * j⁻¹) * v⁻¹ := by group
        _ = (v⁻¹ * x) * (j⁻¹ * v) * v⁻¹ := by rw [hjv]
        _ = (v⁻¹ * x) * j⁻¹ := by group
    rw [e]
    exact (centralizer (L : Set G)).mul_mem hxD ((centralizer (L : Set G)).inv_mem hjD)
  rw [hRD, Subgroup.mem_bot] at hmem
  exact mul_inv_eq_one.1 hmem

end Inner

end CFSG.GH74.AS16.E2
