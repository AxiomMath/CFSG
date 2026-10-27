module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK3Aux2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem toSign_injective' {a b : (ZMod 3)ˣ} (h : toSign a = toSign b) : a = b := by
  revert a b
  decide

theorem sign_restrict_mul (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1) {α : ℤˣ}
    (hty : invType t = (3, α)) :
    quadSign (Q.restrict (fixSp t)) * quadSign (Q.restrict (commSp t)) = -1 := by
  have hWdim : Module.finrank (ZMod 3) (commSp t) = 3 := by
    simpa only [invType, invDim] using congrArg Prod.fst hty
  have hUdim : Module.finrank (ZMod 3) (fixSp t) = 3 := by
    have := finrank_fixSp_add_finrank_commSp (Q := Q) t
    omega
  have h := quadSign_eq_fixSp_commSp hQ htt
  rw [hsgn, hUdim, hWdim] at h
  have h9 : (-1 : ℤˣ) ^ (3 * 3) = -1 := by decide
  rw [h9, mul_neg, mul_one] at h
  rcases Int.units_eq_one_or (quadSign (Q.restrict (fixSp t))) with h1 | h1 <;>
    rcases Int.units_eq_one_or (quadSign (Q.restrict (commSp t))) with h2 | h2
  · rw [h1, h2] at h ⊢
    exact absurd h (by decide)
  · rw [h1, h2]
    decide
  · rw [h1, h2]
    decide
  · rw [h1, h2] at h ⊢
    exact absurd h (by decide)

theorem frameNorm_mul (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1) {α : ℤˣ}
    (hty : invType t = (3, α)) :
    (frameNorm (Q.restrict (fixSp t)) : ZMod 3) *
      (frameNorm (Q.restrict (commSp t)) : ZMod 3) = -1 := by
  have hsign := sign_restrict_mul hQ htt hdim hsgn hty
  have hunit : frameNorm (Q.restrict (fixSp t)) * frameNorm (Q.restrict (commSp t)) = -1 := by
    apply toSign_injective'
    rw [map_mul, toSign_frameNorm, toSign_frameNorm]
    have h : (-(quadSign (Q.restrict (fixSp t)))) * (-(quadSign (Q.restrict (commSp t)))) = -1 := by
      rw [neg_mul_neg, hsign]
    rw [h]
    decide
  rw [← Units.val_mul, hunit]
  rfl

end CFSG.OddStandard.SmallF3.Omega

