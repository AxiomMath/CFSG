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
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
set_option autoImplicit false
namespace CFSG.ClassicalInvolution.Q3.TL4.O264
open QuadraticMap
open scoped MatrixGroups

theorem isPGroup_closure_of_comm_gen {G : Type*} [Group G] {s : Set G}
    (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) (h4 : ∀ x ∈ s, x ^ 4 = 1) :
    IsPGroup 2 ↥(Subgroup.closure s) := by
  have h1 : Subgroup.closure s ≤ Subgroup.centralizer s := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    exact fun y hy => hcomm y hy x hx
  have h2 : Subgroup.closure s ≤ Subgroup.centralizer (Subgroup.closure s) := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    exact ((Subgroup.mem_centralizer_iff.mp (h1 hy)) x hx).symm
  have hc : ∀ x ∈ Subgroup.closure s, ∀ y ∈ Subgroup.closure s, x * y = y * x :=
    fun x hx y hy => (Subgroup.mem_centralizer_iff.mp (h2 hy)) x hx
  have key : ∀ x ∈ Subgroup.closure s, x ^ 4 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact h4 x hx
    | one => exact one_pow _
    | mul x y hx hy ihx ihy => rw [(Commute.mul_pow (hc x hx y hy) 4), ihx, ihy, one_mul]
    | inv x hx ihx => rw [inv_pow, ihx, inv_one]
  intro g
  exact ⟨2, Subtype.ext (by simpa using key g g.2)⟩

theorem two_lt_card_of_three_gen {G : Type*} [Group G] {H : Subgroup G} [Finite ↥H] {a b c : G}
    (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    2 < Nat.card ↥H := by
  have hinj : Function.Injective
      (![⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩] : Fin 3 → ↥H) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Subtype.ext_iff]
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

end CFSG.ClassicalInvolution.Q3.TL4.O264
