module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearAut

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K]

theorem semilinearAutHom_pow_eq_one (h : UnitaryFieldData p f K) {r ε : ℕ} (hr : 1 ≤ r)
    (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε) (x : semilinearSimilitudes h r ε) (m : ℕ)
    (hσ : (x : SemiGL (HypIndex r ε) K).right = RingEquiv.refl K) (c : K) (hc : c ≠ 0)
    (hAm : ((((x : SemiGL (HypIndex r ε) K).left : GL (HypIndex r ε) K) ^ m :
      GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = c • 1) :
    semilinearAutHom h hr hε x ^ m = 1 := by
  rw [← map_pow, semilinearAutHom_eq_one_iff h hr hε hn]
  have hx : (x : SemiGL (HypIndex r ε) K) =
      SemidirectProduct.inl (x : SemiGL (HypIndex r ε) K).left := by
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right (x : SemiGL (HypIndex r ε) K)]
    have : (x : SemiGL (HypIndex r ε) K).right = 1 := hσ
    rw [this, map_one, mul_one]
  have hxm : ((x ^ m : semilinearSimilitudes h r ε) : SemiGL (HypIndex r ε) K) =
      SemidirectProduct.inl (((x : SemiGL (HypIndex r ε) K).left) ^ m) := by
    rw [Subgroup.coe_pow]
    conv_lhs => rw [hx]
    rw [← map_pow]
  refine ⟨?_, Units.mk0 c hc, ?_⟩
  · rw [hxm, SemidirectProduct.right_inl]
    rfl
  · rw [hxm, SemidirectProduct.left_inl]
    apply Units.ext
    rw [hAm, GeneralLinearGroup.coe_scalar, scalar_apply, ← Matrix.smul_one_eq_diagonal]
    rfl

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
