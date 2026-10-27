module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
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

namespace CFSG.HardMathSupport.Cooperstein.Proving

open Equiv

theorem pCore_two_perm_eq_bot_of_five_le {n : ℕ} (hn : 5 ≤ n) :
    CFSG.pCore 2 (Perm (Fin n)) = ⊥ := by
  by_contra h
  have : (CFSG.pCore 2 (Perm (Fin n))).Normal := CFSG.pCore_normal
  have : Nontrivial (CFSG.pCore 2 (Perm (Fin n))) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr h
  have hcard : 5 ≤ Nat.card (Fin n) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    exact hn
  have hA := Equiv.Perm.alternatingGroup_le_of_normal (α := Fin n) hcard
    (N := CFSG.pCore 2 (Perm (Fin n))) inferInstance
  let x0 : Fin n := ⟨0, by omega⟩
  let x1 : Fin n := ⟨1, by omega⟩
  let x2 : Fin n := ⟨2, by omega⟩
  have h01 : x0 ≠ x1 := by simp [x0, x1, Fin.ext_iff]
  have h02 : x0 ≠ x2 := by simp [x0, x2, Fin.ext_iff]
  have h12 : x1 ≠ x2 := by simp [x1, x2, Fin.ext_iff]
  have hc3 : (swap x0 x1 * swap x0 x2).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same h01 h02 h12
  have hcN : swap x0 x1 * swap x0 x2 ∈ CFSG.pCore 2 (Perm (Fin n)) :=
    hA (hc3.mem_alternatingGroup)
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := Perm (Fin n)))
    (⟨swap x0 x1 * swap x0 x2, hcN⟩ : CFSG.pCore 2 (Perm (Fin n)))
  have hck : (swap x0 x1 * swap x0 x2) ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h3 : orderOf (swap x0 x1 * swap x0 x2) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one hck
  rw [hc3.orderOf] at h3
  have h3' : 3 ∣ 2 ^ k := h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3'
  norm_num at this

end CFSG.HardMathSupport.Cooperstein.Proving

end
