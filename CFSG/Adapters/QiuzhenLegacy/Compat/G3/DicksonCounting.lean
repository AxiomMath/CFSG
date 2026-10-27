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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
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

namespace CFSG.Glauberman.Dickson

theorem h826_card_actor_dvd_group_card_sub_one
    {A E : Type*} [Group A] [Finite A] [Group E] [Finite E]
    [MulDistribMulAction A E]
    (hfree : ∀ a : A, a ≠ 1 → ∀ e : E, a • e = e → e = 1) :
    Nat.card A ∣ Nat.card E - 1 := by
  classical
  let X := {e : E // e ≠ 1}
  let : MulAction A X :=
    { smul := fun a e => ⟨a • (e : E), by
        intro h
        apply e.2
        have h' := congrArg (fun x : E => a⁻¹ • x) h
        simpa using h'⟩
      one_smul := by
        intro e
        apply Subtype.ext
        change (1 : A) • (e : E) = (e : E)
        exact one_smul A (e : E)
      mul_smul := by
        intro a b e
        apply Subtype.ext
        change (a * b) • (e : E) = a • (b • (e : E))
        exact mul_smul a b (e : E) }
  have hstab : ∀ e : X, MulAction.stabilizer A e = ⊥ := by
    intro e
    rw [eq_bot_iff]
    intro a ha
    have hae : a • e = e := by
      simpa [MulAction.mem_stabilizer_iff] using ha
    by_contra ha_ne_one
    have hfix : a • (e : E) = (e : E) := congrArg Subtype.val hae
    exact e.2 (hfree a ha_ne_one (e : E) hfix)
  have hcard := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
  have hXcard : Nat.card X = Nat.card E - 1 := by
    let : Fintype E := Fintype.ofFinite E
    let : Fintype X := Fintype.ofFinite X
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    change Fintype.card {e : E // e ≠ 1} = Fintype.card E - 1
    simp
  rw [hXcard, Nat.card_prod] at hcard
  exact ⟨Nat.card (Quotient (MulAction.orbitRel A X)), by
    rw [mul_comm]
    exact hcard⟩

end CFSG.Glauberman.Dickson
