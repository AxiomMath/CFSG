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

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

def cyclicScalarAutEquiv {Cyclic : Type groupUniverse} [Group Cyclic] (modulus : ℕ)
    (coordinates : Multiplicative (ZMod modulus) ≃* Cyclic) :
    MulAut Cyclic ≃* (ZMod modulus)ˣ :=
  (MulAut.congr coordinates.symm).trans
    ((MulAutMultiplicative (ZMod modulus)).trans
      ((AddEquiv.toMultiplicative (ZMod.AddAutEquivUnits modulus)).trans
        (MulEquiv.multiplicativeAdditive (ZMod modulus)ˣ)))

theorem cyclicScalarAutEquiv_symm_apply {Cyclic : Type groupUniverse} [Group Cyclic]
    (modulus : ℕ) (coordinates : Multiplicative (ZMod modulus) ≃* Cyclic)
    (scalar : (ZMod modulus)ˣ) (source : Multiplicative (ZMod modulus)) :
    (cyclicScalarAutEquiv modulus coordinates).symm scalar (coordinates source) =
      coordinates (Multiplicative.ofAdd ((scalar : ZMod modulus) * source.toAdd)) := by
  simp only [cyclicScalarAutEquiv, MulEquiv.symm_trans_apply, MulAut.congr_symm_apply]
  change coordinates (((MulAutMultiplicative (ZMod modulus)).symm
    ((ZMod.AddAutEquivUnits modulus).symm (Additive.ofMul scalar))) (coordinates.symm (coordinates source))) = _
  rw [coordinates.symm_apply_apply]
  rw [ZMod.AddAutEquivUnits_symm_apply]
  change coordinates (Multiplicative.ofAdd ((AddAut.mulLeft scalar) source.toAdd)) = _
  rfl

theorem cyclicScalarAutEquiv_apply {Cyclic : Type groupUniverse} [Group Cyclic]
    (modulus : ℕ) (coordinates : Multiplicative (ZMod modulus) ≃* Cyclic)
    (automorphism : MulAut Cyclic) (source : Multiplicative (ZMod modulus)) :
    automorphism (coordinates source) =
      coordinates (Multiplicative.ofAdd
        (((cyclicScalarAutEquiv modulus coordinates) automorphism : ZMod modulus) * source.toAdd)) := by
  have hformula := cyclicScalarAutEquiv_symm_apply modulus coordinates
    ((cyclicScalarAutEquiv modulus coordinates) automorphism) source
  simpa only [MulEquiv.symm_apply_apply] using hformula

def binaryCongruenceInvolution (exponent : ℕ) : (ZMod (2 ^ (exponent + 3)))ˣ :=
  ZMod.unitOfCoprime (1 + 2 ^ (exponent + 2)) (by
    apply Nat.Coprime.pow_right
    apply Nat.coprime_two_right.mpr
    exact Odd.add_even (by decide : Odd 1) (Even.pow_of_ne_zero (by decide : Even 2) (by omega)))

theorem binaryCongruenceInvolution_val (exponent : ℕ) :
    (binaryCongruenceInvolution exponent : ZMod (2 ^ (exponent + 3))) =
      1 + (2 : ZMod (2 ^ (exponent + 3))) ^ (exponent + 2) := by
  change ((1 + 2 ^ (exponent + 2) : ℕ) : ZMod (2 ^ (exponent + 3))) = _
  push_cast
  rfl

theorem binaryCongruenceInvolution_sq (exponent : ℕ) :
    binaryCongruenceInvolution exponent ^ 2 = 1 := by
  apply Units.ext
  change (binaryCongruenceInvolution exponent : ZMod (2 ^ (exponent + 3))) ^ 2 = 1
  rw [binaryCongruenceInvolution_val]
  have hmodulus : (2 : ZMod (2 ^ (exponent + 3))) ^ (exponent + 3) = 0 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using ZMod.natCast_self (2 ^ (exponent + 3))
  have hlinear : (2 : ZMod (2 ^ (exponent + 3))) * 2 ^ (exponent + 2) = 0 := by
    simpa only [pow_succ'] using hmodulus
  have hquadratic : ((2 : ZMod (2 ^ (exponent + 3))) ^ (exponent + 2)) ^ 2 = 0 := by
    calc
      ((2 : ZMod (2 ^ (exponent + 3))) ^ (exponent + 2)) ^ 2 =
          2 ^ (exponent + 3) * 2 ^ (exponent + 1) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
      _ = 0 := by rw [hmodulus, zero_mul]
  calc
    (1 + (2 : ZMod (2 ^ (exponent + 3))) ^ (exponent + 2)) ^ 2 =
        1 + 2 * 2 ^ (exponent + 2) + (2 ^ (exponent + 2)) ^ 2 := by ring
    _ = 1 := by rw [hlinear, hquadratic]; ring

theorem binaryCongruenceInvolution_ne_one (exponent : ℕ) :
    binaryCongruenceInvolution exponent ≠ 1 := by
  intro hone
  have hval := congrArg (fun scalar : (ZMod (2 ^ (exponent + 3)))ˣ => (scalar : ZMod (2 ^ (exponent + 3)))) hone
  change (binaryCongruenceInvolution exponent : ZMod (2 ^ (exponent + 3))) = 1 at hval
  rw [binaryCongruenceInvolution_val] at hval
  have hzero : (2 : ZMod (2 ^ (exponent + 3))) ^ (exponent + 2) = 0 := by
    linear_combination hval
  have hcastZero : ((2 ^ (exponent + 2) : ℕ) : ZMod (2 ^ (exponent + 3))) = 0 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hzero
  have hdivides := (ZMod.natCast_eq_zero_iff _ _).mp hcastZero
  have hbound := Nat.le_of_dvd (by positivity : 0 < 2 ^ (exponent + 2)) hdivides
  have hstrict : 2 ^ (exponent + 2) < 2 ^ (exponent + 3) :=
    Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
  omega

theorem binaryCongruenceInvolution_mod_four (exponent : ℕ) :
    (ZMod.unitsMap (show 4 ∣ 2 ^ (exponent + 3) from by
      rw [show exponent + 3 = 2 + (exponent + 1) by omega, pow_add]
      exact dvd_mul_right _ _)) (binaryCongruenceInvolution exponent) = 1 := by
  apply Units.ext
  let divides : 4 ∣ 2 ^ (exponent + 3) := by
    rw [show exponent + 3 = 2 + (exponent + 1) by omega, pow_add]
    exact dvd_mul_right _ _
  change (ZMod.castHom divides (ZMod 4)) (binaryCongruenceInvolution exponent :
    ZMod (2 ^ (exponent + 3))) = 1
  rw [binaryCongruenceInvolution_val, map_add, map_one, map_pow, map_ofNat]
  have hzero : (2 : ZMod 4) ^ (exponent + 2) = 0 := by
    calc
      (2 : ZMod 4) ^ (exponent + 2) = (2 : ZMod 4) ^ 2 * 2 ^ exponent := by
        rw [← pow_add]
        congr 1
        omega
      _ = 0 := by
        have hfour : (2 : ZMod 4) ^ 2 = 0 := by decide
        rw [hfour, zero_mul]
  rw [hzero, add_zero]

end CFSG.LargeEvenClassification.Helpers
