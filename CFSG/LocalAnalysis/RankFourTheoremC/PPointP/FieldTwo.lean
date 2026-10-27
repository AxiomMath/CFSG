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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointP

theorem exists_three_squares {F : Type*} [Field F] {p : ℕ} [hp : Fact p.Prime] [CharP F p]
    [Finite F] (hF : Nat.card F = p ^ 2) (hp5 : 5 ≤ p) :
    ∃ γ : F, γ ≠ 0 ∧ (∀ m : ℕ, γ ^ 2 ≠ (m : F)) ∧ (∀ m : ℕ, γ ^ 4 ≠ (m : F)) := by
  classical
  obtain ⟨_⟩ := nonempty_fintype F
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hcardU : Nat.card Fˣ = p ^ 2 - 1 := by rw [Nat.card_units, hF]
  have hord : orderOf (γ : F) = p ^ 2 - 1 := by
    rw [orderOf_units, orderOf_eq_card_of_forall_mem_zpowers hγ, hcardU]
  have hγ0 : (γ : F) ≠ 0 := γ.ne_zero
  have hferm : ∀ m : ℕ, (m : F) ≠ 0 → (m : F) ^ (p - 1) = 1 := by
    intro m hm
    have hm' : (m : ZMod p) ≠ 0 := by
      intro h0
      apply hm
      have : (m : F) = ZMod.castHom (dvd_refl p) F (m : ZMod p) := by simp
      rw [this, h0, map_zero]
    have h1 := ZMod.pow_card_sub_one_eq_one hm'
    have h2 := congrArg (ZMod.castHom (dvd_refl p) F) h1
    rw [map_pow, map_one] at h2
    simpa using h2
  have hlt : p ^ 2 - 1 > 4 * (p - 1) := by
    have : p ^ 2 ≥ 5 * p := by nlinarith
    generalize p ^ 2 = q at this ⊢
    omega
  refine ⟨γ, hγ0, fun m hm => ?_, fun m hm => ?_⟩
  · have hm0 : (m : F) ≠ 0 := by rw [← hm]; exact pow_ne_zero 2 hγ0
    have h1 : (γ : F) ^ (2 * (p - 1)) = 1 := by
      rw [pow_mul, hm]; exact hferm m hm0
    have h2 := Nat.le_of_dvd (by omega) (hord ▸ orderOf_dvd_of_pow_eq_one h1)
    omega
  · have hm0 : (m : F) ≠ 0 := by rw [← hm]; exact pow_ne_zero 4 hγ0
    have h1 : (γ : F) ^ (4 * (p - 1)) = 1 := by
      rw [pow_mul, hm]; exact hferm m hm0
    have h2 := Nat.le_of_dvd (by omega) (hord ▸ orderOf_dvd_of_pow_eq_one h1)
    omega

end CFSG.LocalAnalysis.RankFourTheoremC.PPointP
