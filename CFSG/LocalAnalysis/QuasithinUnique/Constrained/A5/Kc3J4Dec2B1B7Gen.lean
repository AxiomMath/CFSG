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

namespace CFSG.QuasithinUnique.A5

@[expose] noncomputable def cntFix {G X : Type*} [Group G] (R : X → G → Prop) (q : X) (m : G) :
    ℕ :=
  Set.ncard {x : G | R q x ∧ x * m = m * x}

@[expose] def IsGoodPt {G X : Type*} [Group G] (V : Subgroup G) (R : X → G → Prop) (q : X) :
    Prop :=
  ∀ m ∈ V, m ≠ 1 → cntFix R q m = 128

variable {G X : Type*} [Group G] [MulAction G X] (R : X → G → Prop)

theorem cntFix_conj (hR : ∀ (n : G) (q : X) (x : G), R (n • q) (n * x * n⁻¹) ↔ R q x)
    (n : G) (q : X) (m : G) : cntFix R (n • q) m = cntFix R q (n⁻¹ * m * n) := by
  unfold cntFix
  have hset : {x : G | R (n • q) x ∧ x * m = m * x} =
      (fun y => n * y * n⁻¹) '' {y : G | R q y ∧ y * (n⁻¹ * m * n) = (n⁻¹ * m * n) * y} := by
    ext x
    constructor
    · rintro ⟨hx, hxm⟩
      refine ⟨n⁻¹ * x * n, ⟨?_, ?_⟩, by group⟩
      · have e : n * (n⁻¹ * x * n) * n⁻¹ = x := by group
        rw [← hR n q (n⁻¹ * x * n), e]
        exact hx
      · have e : n⁻¹ * x * n * (n⁻¹ * m * n) = n⁻¹ * (x * m) * n := by group
        have e' : n⁻¹ * m * n * (n⁻¹ * x * n) = n⁻¹ * (m * x) * n := by group
        rw [e, e', hxm]
    · rintro ⟨y, ⟨hy, hym⟩, rfl⟩
      refine ⟨(hR n q y).2 hy, ?_⟩
      have e : n * y * n⁻¹ * m = n * (y * (n⁻¹ * m * n)) * n⁻¹ := by group
      have e' : m * (n * y * n⁻¹) = n * ((n⁻¹ * m * n) * y) * n⁻¹ := by group
      rw [e, e', hym]
  rw [hset]
  exact Set.ncard_image_of_injective _ (fun a b h => by simpa using h)

theorem isGoodPt_smul (hR : ∀ (n : G) (q : X) (x : G), R (n • q) (n * x * n⁻¹) ↔ R q x)
    {V : Subgroup G} {n : G} (hn : n ∈ Subgroup.normalizer (V : Set G)) {q : X}
    (h : IsGoodPt V R q) : IsGoodPt V R (n • q) := by
  intro m hm hm1
  rw [cntFix_conj R hR]
  have hm' : n⁻¹ * m * n ∈ V := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) m).1 hm
    simpa using this
  refine h _ hm' fun h1 => hm1 ?_
  have : m = n * (n⁻¹ * m * n) * n⁻¹ := by group
  rw [this, h1]
  group

end CFSG.QuasithinUnique.A5
