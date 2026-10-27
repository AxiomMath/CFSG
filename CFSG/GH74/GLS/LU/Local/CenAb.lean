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

namespace CFSG.GH74.GLS.LU.Local

open Subgroup

@[expose] def LUCenAb {G : Type*} [Group G] (S K : Subgroup G) : Prop :=
  ∀ s ∈ S, s ∈ normalizer (K : Set G) → (∃ k ∈ K, s * k ≠ k * s) →
    ∀ a ∈ K, ∀ b ∈ K, a * s = s * a → b * s = s * b → a * b = b * a

namespace LUCenAb

variable {G H : Type*} [Group G] [Group H]

theorem mono {S S' K : Subgroup G} (hS : S ≤ S') (h : LUCenAb S' K) : LUCenAb S K :=
  fun s hs => h s (hS hs)

theorem map (e : G ≃* H) {S K : Subgroup G} (h : LUCenAb S K) :
    LUCenAb (S.map e.toMonoidHom) (K.map e.toMonoidHom) := by
  intro s' hs' hn hnc a' ha' b' hb' ha hb
  obtain ⟨s, hsS, rfl⟩ := Subgroup.mem_map.mp hs'
  obtain ⟨a, haK, rfl⟩ := Subgroup.mem_map.mp ha'
  obtain ⟨b, hbK, rfl⟩ := Subgroup.mem_map.mp hb'
  simp only [MulEquiv.coe_toMonoidHom] at hn hnc ha hb ⊢
  have hsn : s ∈ normalizer (K : Set G) := by
    rw [mem_normalizer_iff] at hn ⊢
    intro x
    have := hn (e x)
    rw [show e s * e x * (e s)⁻¹ = e (s * x * s⁻¹) by simp] at this
    constructor
    · intro hx
      have h1 : e (s * x * s⁻¹) ∈ K.map e.toMonoidHom := this.mp (Subgroup.mem_map_of_mem _ hx)
      obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp h1
      have := e.injective hye
      rw [← this]; exact hy
    · intro hx
      have h1 : e (s * x * s⁻¹) ∈ K.map e.toMonoidHom := Subgroup.mem_map_of_mem _ hx
      have h2 := this.mpr h1
      obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp h2
      have := e.injective hye
      rw [← this]; exact hy
  obtain ⟨k', hk', hnk⟩ := hnc
  obtain ⟨k, hkK, rfl⟩ := Subgroup.mem_map.mp hk'
  simp only [MulEquiv.coe_toMonoidHom] at hnk
  have hnc' : ∃ k ∈ K, s * k ≠ k * s := ⟨k, hkK, fun hh => hnk (by
    rw [← map_mul, ← map_mul, hh])⟩
  have hab : a * b = b * a := h s hsS hsn hnc' a haK b hbK
    (e.injective (by rw [map_mul, map_mul]; exact ha)) (e.injective (by rw [map_mul, map_mul]; exact hb))
  rw [← map_mul, ← map_mul, hab]

theorem map_conj {S K : Subgroup G} (h : LUCenAb S K) (t : G) :
    LUCenAb (S.map (MulAut.conj t).toMonoidHom) (K.map (MulAut.conj t).toMonoidHom) :=
  h.map (MulAut.conj t)

end LUCenAb

end CFSG.GH74.GLS.LU.Local
