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
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
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

namespace CFSG.ComponentClassification.Sol78

open Equiv Equiv.Perm Subgroup

theorem card_le_factorial_index {H : Type*} [Group H] [Finite H] [IsSimpleGroup H]
    {K : Subgroup H} (hK : K ≠ ⊤) : Nat.card H ≤ K.index.factorial := by
  have hcore : K.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K.normalCore with h | h
    · exact h
    · exfalso
      have h1 := K.normalCore_le
      rw [h] at h1
      exact hK (top_le_iff.mp h1)
  have hinj : Function.Injective (MulAction.toPermHom H (H ⧸ K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker, hcore]
  calc Nat.card H ≤ Nat.card (Perm (H ⧸ K)) := Nat.card_le_card_of_injective _ hinj
    _ = K.index.factorial := by rw [Nat.card_perm]; rfl

theorem le_index_of_mulEquiv_alternating {H : Type*} [Group H] [Finite H] {m : ℕ} (hm : 5 ≤ m)
    (e : H ≃* alternatingGroup (Fin m)) {K : Subgroup H} (hK : K ≠ ⊤) : m ≤ K.index := by
  have : IsSimpleGroup (alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by simpa using hm)
  have : IsSimpleGroup H := e.isSimpleGroup
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h1 := card_le_factorial_index hK
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin] at h1
  by_contra hlt
  rw [not_le] at hlt
  have h2 : K.index.factorial ≤ (m - 1).factorial := Nat.factorial_le (by omega)
  have h3 : m * (m - 1).factorial = m.factorial := Nat.mul_factorial_pred (by omega)
  have hpos := Nat.factorial_pos (m - 1)
  have h4 : m.factorial / 2 < (m - 1).factorial + 1 := by omega
  rw [Nat.div_lt_iff_lt_mul (by norm_num), ← h3] at h4
  nlinarith

end CFSG.ComponentClassification.Sol78
