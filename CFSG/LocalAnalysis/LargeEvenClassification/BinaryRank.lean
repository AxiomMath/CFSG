module

public import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

open scoped MatrixGroups

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem card_linear_aut_binary (Space : Type groupUniverse) [AddCommGroup Space]
    [Module (ZMod 2) Space] [Finite Space] :
    Nat.card (Space ≃ₗ[ZMod 2] Space) =
      Nat.card (GL (Fin (Module.finrank (ZMod 2) Space)) (ZMod 2)) := by
  classical
  let basis := Module.finBasis (ZMod 2) Space
  let equivalence := (Matrix.GeneralLinearGroup.toLin' basis).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Space)
  exact (Nat.card_congr equivalence.toEquiv).symm

theorem card_dvd_of_injective_hom {Source : Type groupUniverse} [Group Source]
    {Target : Type groupUniverse} [Group Target] (embedding : Source →* Target)
    (hinjective : Function.Injective embedding) : Nat.card Source ∣ Nat.card Target := by
  have hequivalence : Source ≃* embedding.range :=
    MonoidHom.ofInjective hinjective
  rw [Nat.card_congr hequivalence.toEquiv]
  exact embedding.range.card_subgroup_dvd_card

theorem binary_GL_small_card_dvd {dimension : ℕ} (hdimension : dimension ≤ 4) :
    Nat.card (GL (Fin dimension) (ZMod 2)) ∣ 20160 := by
  rw [Matrix.card_GL_field]
  interval_cases dimension <;> norm_num [Fin.prod_univ_succ]

theorem odd_prime_cube_not_dvd_20160 {prime : ℕ} (hprime : prime.Prime) (hodd : prime ≠ 2) :
    ¬ prime ^ 3 ∣ 20160 := by
  intro hcube
  have hdivides : prime ∣ 20160 := by
    have hpower : prime ∣ prime ^ 3 := by
      exact dvd_pow_self prime (by decide : 3 ≠ 0)
    exact hpower.trans hcube
  have hprimeOptions : prime = 2 ∨ prime = 3 ∨ prime = 5 ∨ prime = 7 := by
    have hfactorization : 20160 = 2 ^ 6 * 3 ^ 2 * 5 * 7 := by norm_num
    rw [hfactorization] at hdivides
    rcases hprime.dvd_mul.mp hdivides with hfirst | hseven
    · rcases hprime.dvd_mul.mp hfirst with hsecond | hfive
      · rcases hprime.dvd_mul.mp hsecond with htwo | hthree
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp
            (hprime.dvd_of_dvd_pow htwo))
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hprime (by norm_num)).mp
            (hprime.dvd_of_dvd_pow hthree)))
      · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hprime (by norm_num)).mp hfive)))
    · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hprime (by norm_num)).mp hseven)))
  rcases hprimeOptions with htwo | hthree | hfive | hseven
  · exact hodd htwo
  · subst prime
    norm_num at hcube
  · subst prime
    norm_num at hcube
  · subst prime
    norm_num at hcube

theorem faithful_odd_rank_three_binary_dimension {Acting Space : Type groupUniverse}
    [Group Acting] [AddCommGroup Space] [Module (ZMod 2) Space] [Finite Space]
    {prime rank : ℕ} (hprime : prime.Prime) (hodd : prime ≠ 2) (hrank : 3 ≤ rank)
    (hcard : Nat.card Acting = prime ^ rank)
    (action : Acting →* (Space ≃ₗ[ZMod 2] Space)) (hinjective : Function.Injective action) :
    5 ≤ Module.finrank (ZMod 2) Space := by
  by_contra hsmall
  have hdimension : Module.finrank (ZMod 2) Space ≤ 4 := by omega
  have hdivides := card_dvd_of_injective_hom action hinjective
  rw [hcard, card_linear_aut_binary] at hdivides
  have hcubeDivides : prime ^ 3 ∣ 20160 :=
    (Nat.pow_dvd_pow prime hrank).trans (hdivides.trans (binary_GL_small_card_dvd hdimension))
  exact odd_prime_cube_not_dvd_20160 hprime hodd hcubeDivides

end CFSG.LargeEvenClassification.Helpers
