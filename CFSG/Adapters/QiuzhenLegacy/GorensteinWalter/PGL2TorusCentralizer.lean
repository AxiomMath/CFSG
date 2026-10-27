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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.GorensteinWalter

universe u

lemma two_ne_zero_of_odd_card (K : Type u) [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) : (2 : K) ≠ 0 := by
  intro h2
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd_char : ringChar K ∣ 2 := (CharP.cast_eq_zero_iff K (ringChar K) 2).mp h2
  have hchar2 : ringChar K = 2 := by
    rcases hdvd_char with ⟨c, hc⟩
    cases c with
    | zero => norm_num at hc
    | succ c =>
        cases c with
        | zero => omega
        | succ c =>
            exfalso
            have hrc_pos : 0 < ringChar K := by
              by_contra h
              have hz : ringChar K = 0 := by omega
              rw [hz] at hc
              norm_num at hc
            have hrc_le : ringChar K ≤ 1 := by nlinarith
            have hrc1 : ringChar K = 1 := by omega
            have hsub : Subsingleton K := (ringChar.ringChar_eq_one (R := K)).mp hrc1
            exact not_subsingleton K hsub
  have hdvd_card : 2 ∣ Fintype.card K :=
    (prime_dvd_char_iff_dvd_card (R := K) (p := 2)).mp (by simp [hchar2])
  have hprime_dvd : (2 : ℕ) ∣ Nat.card K := by
    simpa [Nat.card_eq_fintype_card] using hdvd_card
  exact hodd.not_two_dvd_nat hprime_dvd

end CFSG.GorensteinWalter
