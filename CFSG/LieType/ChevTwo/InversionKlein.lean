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

public section

namespace CFSG.LieType.ChevTwo

theorem exists_both_ne_one {R : Type*} [Group R]
    (hR : ∀ x y : R, x ^ 2 = 1 → y ^ 2 = 1 → x ≠ 1 → y ≠ 1 → x = y)
    {A : Type*} [Group A] (hA2 : ∀ a : A, a ^ 2 = 1) (hcard : Nat.card A = 4)
    (Θ : A →* R × Multiplicative (ZMod 2)) (hΘ : Function.Injective Θ) :
    ∃ a : A, (Θ a).1 ≠ 1 ∧ (Θ a).2 ≠ 1 := by
  by_contra hcon
  have hcon' : ∀ a : A, (Θ a).1 ≠ 1 → (Θ a).2 = 1 := by
    intro a ha
    by_contra h2
    exact hcon ⟨a, ha, h2⟩
  have hZ : ∀ x y : Multiplicative (ZMod 2), x ≠ 1 → y ≠ 1 → x = y := by
    decide
  have hsq : ∀ c : A, (Θ c).1 ^ 2 = 1 := by
    intro c
    have h1 : Θ c ^ 2 = 1 := by rw [← map_pow, hA2 c, map_one]
    have h2 : (MonoidHom.fst R (Multiplicative (ZMod 2))) (Θ c ^ 2) = 1 := by
      rw [h1, map_one]
    rw [map_pow] at h2
    exact h2
  have hXX : ∀ a b : A, a ≠ 1 → b ≠ 1 → a ≠ b → (Θ a).1 = 1 → (Θ b).1 = 1 → False := by
    intro a b ha hb hab ha1 hb1
    have hae : (Θ a).2 ≠ 1 := by
      intro h
      apply ha
      apply hΘ
      rw [map_one]
      exact Prod.ext ha1 h
    have hbe : (Θ b).2 ≠ 1 := by
      intro h
      apply hb
      apply hΘ
      rw [map_one]
      exact Prod.ext hb1 h
    exact hab (hΘ (Prod.ext (ha1.trans hb1.symm) (hZ _ _ hae hbe)))
  have hYY : ∀ a b : A, a ≠ 1 → b ≠ 1 → a ≠ b → (Θ a).1 ≠ 1 → (Θ b).1 ≠ 1 → False := by
    intro a b _ _ hab ha1 hb1
    have ha2 : (Θ a).2 = 1 := hcon' a ha1
    have hb2 : (Θ b).2 = 1 := hcon' b hb1
    exact hab (hΘ (Prod.ext (hR _ _ (hsq a) (hsq b) ha1 hb1) (ha2.trans hb2.symm)))
  have hsame : ∀ a b : A, a ≠ 1 → b ≠ 1 → a ≠ b →
      ((Θ a).1 = 1 ↔ (Θ b).1 = 1) → False := by
    intro a b ha hb hab hiff
    by_cases h : (Θ a).1 = 1
    · exact hXX a b ha hb hab h (hiff.1 h)
    · exact hYY a b ha hb hab h (fun h' => h (hiff.2 h'))
  classical
  have hfin : Finite A := Nat.finite_of_card_ne_zero (by omega)
  letI : Fintype A := Fintype.ofFinite A
  have hcardF : Fintype.card A = 4 := by rw [← Nat.card_eq_fintype_card, hcard]
  have hs : 2 < ((Finset.univ : Finset A).erase 1).card := by
    have h1 := Finset.card_erase_of_mem (Finset.mem_univ (1 : A))
    rw [Finset.card_univ, hcardF] at h1
    omega
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := Finset.two_lt_card.1 hs
  have hp1 : p ≠ 1 := (Finset.mem_erase.1 hp).1
  have hq1 : q ≠ 1 := (Finset.mem_erase.1 hq).1
  have hr1 : r ≠ 1 := (Finset.mem_erase.1 hr).1
  by_cases h1 : (Θ p).1 = 1
  · by_cases h2 : (Θ q).1 = 1
    · exact hsame p q hp1 hq1 hpq ⟨fun _ => h2, fun _ => h1⟩
    · by_cases h3 : (Θ r).1 = 1
      · exact hsame p r hp1 hr1 hpr ⟨fun _ => h3, fun _ => h1⟩
      · exact hsame q r hq1 hr1 hqr ⟨fun h => absurd h h2, fun h => absurd h h3⟩
  · by_cases h2 : (Θ q).1 = 1
    · by_cases h3 : (Θ r).1 = 1
      · exact hsame q r hq1 hr1 hqr ⟨fun _ => h3, fun _ => h2⟩
      · exact hsame p r hp1 hr1 hpr ⟨fun h => absurd h h1, fun h => absurd h h3⟩
    · exact hsame p q hp1 hq1 hpq ⟨fun h => absurd h h1, fun h => absurd h h2⟩

end CFSG.LieType.ChevTwo
