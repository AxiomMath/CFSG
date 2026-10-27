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
public import Mathlib.GroupTheory.NoncommCoprod
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

namespace CFSG.GH74.GLS.Stage4.Q3n

theorem card_sup_mul_card_inf {G : Type} [Group G] [Finite G] {A B : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  let μ : A × B →* G :=
    MonoidHom.noncommCoprod A.subtype B.subtype fun x y => hcomm x x.2 y y.2
  have hμ : ∀ x : A × B, μ x = (x.1 : G) * x.2 := fun _ => rfl
  have hrange : μ.range = A ⊔ B := by
    refine (MonoidHom.noncommCoprod_range A.subtype B.subtype _).trans ?_
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
  have hker : Nat.card μ.ker = Nat.card ↥(A ⊓ B) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : G), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : G)⁻¹, B.inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact B.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_inv_eq] at h
      exact Subtype.ext (Prod.ext rfl (Subtype.ext h))
  have h := Subgroup.card_ker_mul_card_range μ
  rw [hrange, hker, Nat.card_prod] at h
  rwa [mul_comm]

end CFSG.GH74.GLS.Stage4.Q3n
