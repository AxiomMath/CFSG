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

namespace CFSG.LargeEvenClassification.Helpers

theorem zmod_hom_apply_nat {modulus : ℕ} [NeZero modulus] {Target : Type*}
    [AddMonoid Target] (homomorphism : ZMod modulus →+ Target) (element : ZMod modulus) :
    homomorphism element = element.val • homomorphism 1 := by
  have hexpression : element.val • (1 : ZMod modulus) = element := by
    simpa only [nsmul_eq_mul, mul_one] using ZMod.natCast_zmod_val element
  calc
    _ = homomorphism (element.val • (1 : ZMod modulus)) := congrArg homomorphism hexpression.symm
    _ = _ := map_nsmul homomorphism _ _

@[expose] def scaledCyclicInclusion (scale modulus : ℕ) : ZMod modulus →+ ZMod (scale * modulus) :=
  ZMod.lift modulus ⟨zmultiplesHom (ZMod (scale * modulus)) (scale : ZMod (scale * modulus)), by
    change (modulus : ℤ) • (scale : ZMod (scale * modulus)) = 0
    simp only [zsmul_eq_mul, Int.cast_natCast]
    rw [← Nat.cast_mul, Nat.mul_comm modulus scale, ZMod.natCast_self]⟩

theorem scaledCyclicInclusion_one (scale modulus : ℕ) :
    scaledCyclicInclusion scale modulus 1 = (scale : ZMod (scale * modulus)) := by
  unfold scaledCyclicInclusion
  rw [show (1 : ZMod modulus) = ((1 : ℤ) : ZMod modulus) by simp, ZMod.lift_coe]
  simp only [zmultiplesHom_apply, one_zsmul]

theorem scaledCyclicInclusion_apply (scale modulus : ℕ) [NeZero modulus]
    (element : ZMod modulus) :
    scaledCyclicInclusion scale modulus element =
      (scale : ZMod (scale * modulus)) * (element.val : ZMod (scale * modulus)) := by
  rw [zmod_hom_apply_nat, scaledCyclicInclusion_one, nsmul_eq_mul]
  exact mul_comm _ _

theorem scaledCyclicInclusion_injective (scale modulus : ℕ) [NeZero modulus]
    (hscale : 0 < scale) : Function.Injective (scaledCyclicInclusion scale modulus) := by
  intro first second heq
  rw [scaledCyclicInclusion_apply, scaledCyclicInclusion_apply,
    ← Nat.cast_mul, ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff',
    Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at heq
  have hvalues : first.val % modulus = second.val % modulus :=
    Nat.eq_of_mul_eq_mul_left hscale heq
  rw [Nat.mod_eq_of_lt (ZMod.val_lt first), Nat.mod_eq_of_lt (ZMod.val_lt second)] at hvalues
  exact ZMod.val_injective modulus hvalues

theorem scaledCyclicInclusion_range (scale modulus : ℕ) [NeZero modulus]
    (hscale : 0 < scale) (element : ZMod (scale * modulus))
    (hannihilated : (modulus : ZMod (scale * modulus)) * element = 0) :
    ∃ source : ZMod modulus, scaledCyclicInclusion scale modulus source = element := by
  let : NeZero (scale * modulus) := ⟨Nat.ne_of_gt (Nat.mul_pos hscale (NeZero.pos modulus))⟩
  have hdivides : scale * modulus ∣ modulus * element.val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa only [Nat.cast_mul, ZMod.natCast_zmod_val] using hannihilated
  have hscaleDivides : scale ∣ element.val := by
    apply Nat.dvd_of_mul_dvd_mul_right (NeZero.pos modulus)
    simpa only [Nat.mul_comm modulus] using hdivides
  have hquotientLt : element.val / scale < modulus :=
    (Nat.div_lt_iff_lt_mul hscale).mpr (by
      simpa only [Nat.mul_comm] using ZMod.val_lt element)
  refine ⟨(element.val / scale : ℕ), ?_⟩
  rw [scaledCyclicInclusion_apply, ZMod.val_natCast, Nat.mod_eq_of_lt hquotientLt,
    ← Nat.cast_mul, Nat.mul_div_cancel' hscaleDivides, ZMod.natCast_zmod_val]

@[expose] def cyclicReduction (scale modulus : ℕ) : ZMod (scale * modulus) →+* ZMod modulus :=
  ZMod.castHom (dvd_mul_left modulus scale) (ZMod modulus)

theorem cyclicReduction_apply (scale modulus : ℕ) [NeZero (scale * modulus)]
    (element : ZMod (scale * modulus)) :
    cyclicReduction scale modulus element = (element.val : ZMod modulus) := by
  calc
    _ = cyclicReduction scale modulus (element.val : ZMod (scale * modulus)) :=
      congrArg (cyclicReduction scale modulus) (ZMod.natCast_zmod_val element).symm
    _ = _ := map_natCast _ _

theorem cyclicReduction_inclusion (scale modulus : ℕ) [NeZero modulus]
    (element : ZMod modulus) :
    cyclicReduction scale modulus (scaledCyclicInclusion scale modulus element) =
      (scale : ZMod modulus) * element := by
  rw [scaledCyclicInclusion_apply, map_mul, map_natCast, map_natCast,
    ZMod.natCast_zmod_val]

theorem scaledCyclicInclusion_scalar (scale modulus : ℕ) [NeZero modulus]
    [NeZero (scale * modulus)] (scalar : ZMod (scale * modulus))
    (element : ZMod modulus) :
    scaledCyclicInclusion scale modulus (cyclicReduction scale modulus scalar * element) =
      scalar * scaledCyclicInclusion scale modulus element := by
  have hscalar : scalar.val • element = cyclicReduction scale modulus scalar * element := by
    rw [nsmul_eq_mul, cyclicReduction_apply]
  rw [← hscalar, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]

end CFSG.LargeEvenClassification.Helpers
