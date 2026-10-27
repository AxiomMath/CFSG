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

namespace CFSG.ClassicalInvolution

variable {G : Type*} [Group G] [Finite G]

theorem mem_normalizer_closure_of_conj_mem (A : Set G) (g : G)
    (h : ∀ a ∈ A, g * a * g⁻¹ ∈ Subgroup.closure A) :
    g ∈ Subgroup.normalizer (Subgroup.closure A : Set G) := by
  set U := Subgroup.closure A
  set φ : G →* G := (MulAut.conj g).toMonoidHom with hφ
  have hle : U ≤ U.comap φ := (Subgroup.closure_le _).2 fun a ha => h a ha
  have hmap : U.map φ ≤ U := Subgroup.map_le_iff_le_comap.2 hle
  have hinj : Function.Injective φ := (MulAut.conj g).injective
  have heq : U.map φ = U :=
    Subgroup.eq_of_le_of_card_ge hmap (by rw [Subgroup.card_map_of_injective hinj])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hle hx
  · intro hx
    have hx' : φ x ∈ U.map φ := by
      rw [heq]
      exact hx
    obtain ⟨y, hy, hyx⟩ := hx'
    have : y = x := hinj hyx
    rw [← this]
    exact hy

theorem closure_le_normalizer_closure (B A : Set G)
    (h : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ Subgroup.closure A) :
    Subgroup.closure B ≤ Subgroup.normalizer (Subgroup.closure A : Set G) :=
  (Subgroup.closure_le _).2 fun b hb => mem_normalizer_closure_of_conj_mem A b (h b hb)

end CFSG.ClassicalInvolution
