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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

section Lift

variable {G : Type*} [Group G] {Z : Subgroup G} [Z.Normal]

theorem exists_involution_lift (hcent : Z ≤ Subgroup.center G) (hZ3 : ∀ z ∈ Z, z ^ 3 = 1)
    (σ : G ≃* G) (hσZ : ∀ z ∈ Z, σ z = z) {T : G} (hT2 : T ^ 2 ∈ Z)
    (hσT : ((σ T : G) : G ⧸ Z) = (T : G ⧸ Z)) :
    ∃ T' : G, T' * T' = 1 ∧ (T' : G ⧸ Z) = (T : G ⧸ Z) ∧ σ T' = T' := by
  have hcomm : ∀ {z : G}, z ∈ Z → ∀ g : G, g * z = z * g := fun hz g =>
    Subgroup.mem_center_iff.1 (hcent hz) g
  have hκ : (σ T)⁻¹ * T ∈ Z := by
    rw [← QuotientGroup.eq]
    exact hσT
  have hσT' : σ T = T := by
    set κ := (σ T)⁻¹ * T with hκdef
    have hσTκ : σ T = T * κ⁻¹ := by
      rw [hκdef]
      group
    have hκc : Commute T κ⁻¹ := hcomm (Z.inv_mem hκ) T
    have hσ2 : σ T ^ 2 = T ^ 2 := by
      rw [← map_pow]
      exact hσZ _ hT2
    have h1 : κ⁻¹ ^ 2 = 1 := by
      have : T ^ 2 * κ⁻¹ ^ 2 = T ^ 2 := by
        rw [← hκc.mul_pow, ← hσTκ, hσ2]
      simpa using this
    have hκ2 : κ ^ 2 = 1 := by
      have := congrArg (fun x => x⁻¹) h1
      simpa [inv_pow] using this
    have hκ3 : κ ^ 3 = 1 := hZ3 κ hκ
    have hκ1 : κ = 1 := by
      calc κ = κ ^ 3 * (κ ^ 2)⁻¹ := by group
        _ = 1 := by rw [hκ3, hκ2]; simp
    rw [hσTκ, hκ1]
    simp
  refine ⟨T ^ 3, ?_, ?_, ?_⟩
  · have : T ^ 3 * T ^ 3 = (T ^ 2) ^ 3 := by group
    rw [this]
    exact hZ3 _ hT2
  · have h1 : ((T ^ 2 : G) : G ⧸ Z) = 1 := (QuotientGroup.eq_one_iff _).2 hT2
    rw [QuotientGroup.mk_pow]
    calc (T : G ⧸ Z) ^ 3 = ((T : G ⧸ Z) ^ 2) * (T : G ⧸ Z) := by group
      _ = (T : G ⧸ Z) := by rw [← QuotientGroup.mk_pow, h1, one_mul]
  · rw [map_pow, hσT']

theorem inverted_three_of_lifts (hcent : Z ≤ Subgroup.center G) (hZ3 : ∀ z ∈ Z, z ^ 3 = 1)
    {T Y : G} (hT : T * T = 1) (hY : Y * Y = 1) (hbraid : T * Y * T = Y * T * Y)
    (hne : Y ≠ T) :
    ((T * Y : G) : G ⧸ Z) ^ 3 = 1 ∧ ((T * Y : G) : G ⧸ Z) ≠ 1 ∧
      (T : G ⧸ Z) * ((T * Y : G) : G ⧸ Z) * (T : G ⧸ Z)⁻¹ = ((T * Y : G) : G ⧸ Z)⁻¹ := by
  have hcomm : ∀ {z : G}, z ∈ Z → ∀ g : G, g * z = z * g := fun hz g =>
    Subgroup.mem_center_iff.1 (hcent hz) g
  have hT' : T⁻¹ = T := inv_eq_of_mul_eq_one_right hT
  have hY' : Y⁻¹ = Y := inv_eq_of_mul_eq_one_right hY
  have hcube : (T * Y) ^ 3 = 1 := by
    calc (T * Y) ^ 3 = (T * Y * T) * (Y * T * Y) := by
          simp only [pow_succ, pow_zero, one_mul]
          group
      _ = (T * Y * T) * (T * Y * T) := by rw [← hbraid]
      _ = T * Y * (T * T) * Y * T := by group
      _ = 1 := by
        rw [hT, mul_one, mul_assoc T Y Y, hY, mul_one, hT]
  refine ⟨?_, ?_, ?_⟩
  · rw [← QuotientGroup.mk_pow, hcube, QuotientGroup.mk_one]
  · intro h1
    have hmem : T * Y ∈ Z := (QuotientGroup.eq_one_iff _).1 h1
    have hcT : T * (T * Y) = (T * Y) * T := hcomm hmem T
    have hYκ : Y = T * (T * Y) := by rw [← mul_assoc, hT, one_mul]
    have hκ2 : (T * Y) ^ 2 = 1 := by
      calc (T * Y) ^ 2 = (T * Y) * (T * Y) := pow_two _
        _ = (T * T) * (T * Y) * (T * Y) := by rw [hT, one_mul]
        _ = T * (T * (T * Y)) * (T * Y) := by rw [mul_assoc T T]
        _ = T * ((T * Y) * T) * (T * Y) := by rw [hcT]
        _ = (T * (T * Y)) * (T * (T * Y)) := by group
        _ = Y * Y := by rw [← hYκ]
        _ = 1 := hY
    have hκ1 : T * Y = 1 := by
      calc T * Y = (T * Y) ^ 3 * ((T * Y) ^ 2)⁻¹ := by group
        _ = 1 := by rw [hcube, hκ2]; simp
    exact hne (mul_left_cancel (hκ1.trans hT.symm))
  · rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
    rw [mul_inv_rev, hY', hT', ← mul_assoc T T Y, hT, one_mul]

end Lift

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
