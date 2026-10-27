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

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionAffineOddPair

variable {Ω : Type*}

@[expose] def RegularOnEntire (F : Subgroup (Equiv.Perm Ω)) (Q : Subgroup F) : Prop :=
  ∀ α β : Ω, ∃! q : Q, ((q : F) : Equiv.Perm Ω) α = β

theorem regular_coordinates_bijective
    (F : Subgroup (Equiv.Perm Ω)) (Q : Subgroup F)
    (hreg : RegularOnEntire F Q) (α : Ω) :
    Function.Bijective (fun q : Q => ((q : F) : Equiv.Perm Ω) α) := by
  constructor
  · intro q r hqr
    obtain ⟨s, hs, huniq⟩ := hreg α (((q : F) : Equiv.Perm Ω) α)
    exact (huniq q rfl).trans (huniq r hqr.symm).symm
  · intro β
    obtain ⟨q, hq, _⟩ := hreg α β
    exact ⟨q, hq⟩

theorem regular_card_eq_degree [Finite Ω]
    (F : Subgroup (Equiv.Perm Ω)) (Q : Subgroup F)
    (hreg : RegularOnEntire F Q) (α : Ω) : Nat.card Q = Nat.card Ω :=
  Nat.card_congr (Equiv.ofBijective _ (regular_coordinates_bijective F Q hreg α))

theorem pair_fixed_regular_transporter_commutes
    (F : Subgroup (Equiv.Perm Ω)) (Q : Subgroup F) [Q.Normal]
    (hreg : RegularOnEntire F Q) (α β : Ω) (q : Q)
    (hq : ((q : F) : Equiv.Perm Ω) α = β) (f : F)
    (hα : (f : Equiv.Perm Ω) α = α) (hβ : (f : Equiv.Perm Ω) β = β) :
    Commute f (q : F) := by
  let q' : Q := ⟨f * (q : F) * f⁻¹,
    Subgroup.Normal.conj_mem inferInstance (q : F) q.property f⟩
  have hinv : (f : Equiv.Perm Ω)⁻¹ α = α := by
    exact (f : Equiv.Perm Ω).symm_apply_eq.mpr hα.symm
  have hq' : ((q' : F) : Equiv.Perm Ω) α = β := by
    change (f : Equiv.Perm Ω) (((q : F) : Equiv.Perm Ω)
      ((f : Equiv.Perm Ω)⁻¹ α)) = β
    rw [hinv, hq, hβ]
  have heq : q' = q :=
    (regular_coordinates_bijective F Q hreg α).1 (hq'.trans hq.symm)
  have hconj : f * (q : F) * f⁻¹ = (q : F) := congrArg Subtype.val heq
  exact (mul_inv_eq_iff_eq_mul.mp hconj)

theorem pair_fixed_regular_transporter_powers
    (F : Subgroup (Equiv.Perm Ω)) (Q : Subgroup F) [Q.Normal]
    (hreg : RegularOnEntire F Q) (α β : Ω) (q : Q)
    (hq : ((q : F) : Equiv.Perm Ω) α = β) (f : F)
    (hα : (f : Equiv.Perm Ω) α = α) (hβ : (f : Equiv.Perm Ω) β = β)
    (n : ℕ) :
    (f : Equiv.Perm Ω) ((((q ^ n : Q) : F) : Equiv.Perm Ω) α) =
      ((((q ^ n : Q) : F) : Equiv.Perm Ω) α) := by
  have hc := (pair_fixed_regular_transporter_commutes F Q hreg α β q hq f hα hβ).pow_right n
  have heq := congrArg (fun k : F => (k : Equiv.Perm Ω) α) hc.eq
  change (f : Equiv.Perm Ω) ((((q ^ n : Q) : F) : Equiv.Perm Ω) α) =
    ((((q ^ n : Q) : F) : Equiv.Perm Ω) ((f : Equiv.Perm Ω) α)) at heq
  exact heq.trans (congrArg (fun x => ((((q ^ n : Q) : F) : Equiv.Perm Ω) x)) hα)

end CFSG.ProperTwoGeneratedCore.LocalCriterionAffineOddPair
