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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v w

theorem normal_permutation_common_fixed_set_invariant {actor : Type u} {points : Type v}
    [Group actor] (action : actor →* Equiv.Perm points)
    (normal : Subgroup actor) [normal.Normal] (member : actor) (point : points) :
    (∀ element : normal, action element (action member point) = action member point) ↔
      ∀ element : normal, action element point = point := by
  have hforward : ∀ actorMember : actor, ∀ fixedPoint : points,
      (∀ element : normal, action element fixedPoint = fixedPoint) →
        ∀ element : normal, action element (action actorMember fixedPoint) = action actorMember fixedPoint := by
    intro actorMember fixedPoint hfixed element
    let conjugate : normal := ⟨actorMember⁻¹ * (element : actor) * actorMember,
      (inferInstance : normal.Normal).conj_mem' element element.property actorMember⟩
    have hconjugate : action (conjugate : actor) fixedPoint = fixedPoint := hfixed conjugate
    have heq : (element : actor) * actorMember = actorMember * (conjugate : actor) := by
      dsimp [conjugate]
      group
    calc
      action (element : actor) (action actorMember fixedPoint) =
          action ((element : actor) * actorMember) fixedPoint := by rw [map_mul]; rfl
      _ = action (actorMember * (conjugate : actor)) fixedPoint := by rw [heq]
      _ = action actorMember (action (conjugate : actor) fixedPoint) := by rw [map_mul]; rfl
      _ = action actorMember fixedPoint := by rw [hconjugate]
  constructor
  · intro hfixed
    have hresult := hforward member⁻¹ (action member point) hfixed
    have heq : action member⁻¹ (action member point) = point := by
      rw [map_inv]
      exact (action member).symm_apply_apply point
    rw [heq] at hresult
    exact hresult
  · exact hforward member point

theorem normal_permutation_unique_common_fixed_point_global {actor : Type u} {points : Type v}
    [Group actor] (action : actor →* Equiv.Perm points)
    (normal : Subgroup actor) [normal.Normal] (point : points)
    (hfixed : ∀ element : normal, action element point = point)
    (hunique : ∀ other : points, (∀ element : normal, action element other = other) → other = point) :
    ∀ member : actor, action member point = point := by
  intro member
  apply hunique
  exact (normal_permutation_common_fixed_set_invariant action normal member point).mpr hfixed

theorem prime_power_element_map_eq_one_of_coprime_card {actor : Type u} {target : Type v}
    [Group actor] [Group target] [Finite target]
    (homomorphism : actor →* target) (prime : ℕ) (hprime : prime.Prime)
    (hcoprime : ¬prime ∣ Nat.card target) (member : actor)
    (exponent : ℕ) (hpower : member ^ (prime ^ exponent) = 1) : homomorphism member = 1 := by
  have horderCard := orderOf_dvd_natCard (homomorphism member)
  have horderPrime : orderOf (homomorphism member) ∣ prime ^ exponent := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hpower, map_one]
  have hcoprimePowers : Nat.Coprime (prime ^ exponent) (Nat.card target) :=
    ((hprime.coprime_iff_not_dvd).mpr hcoprime).pow_left exponent
  have horderOne : orderOf (homomorphism member) = 1 := by
    apply Nat.eq_one_of_dvd_one
    have hdivisor := Nat.dvd_gcd horderPrime horderCard
    rw [hcoprimePowers.gcd_eq_one] at hdivisor
    exact hdivisor
  exact orderOf_eq_one_iff.mp horderOne

theorem prime_generated_permutation_action_trivial_of_coprime_card {actor : Type u} {points : Type v}
    [Group actor] [Finite points] (action : actor →* Equiv.Perm points)
    (prime : ℕ) (hprime : prime.Prime) (hcoprime : ¬prime ∣ Nat.card (Equiv.Perm points))
    (hgenerated : Subgroup.closure {member : actor | ∃ exponent : ℕ,
      member ^ (prime ^ exponent) = 1} = ⊤) : ∀ member : actor, action member = 1 := by
  have hkernel : (⊤ : Subgroup actor) ≤ action.ker := by
    rw [← hgenerated]
    apply (Subgroup.closure_le action.ker).mpr
    rintro member ⟨exponent, hpower⟩
    exact prime_power_element_map_eq_one_of_coprime_card action prime hprime hcoprime member exponent hpower
  intro member
  exact hkernel (Subgroup.mem_top member)

end CFSG.RankThreeEvenClassification.Helpers
