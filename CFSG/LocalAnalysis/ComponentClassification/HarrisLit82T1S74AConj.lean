module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74AIbar

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin
open scoped MatrixGroups

variable (K : Type) [Field K]

theorem coe_iBar_mul_longPair_true_X :
    (iBar K : CliffordAlgebra (quadOdd 3 K)) *
        ((oddFrame 3 K).toHypFrame.longPair fin3_zero_ne_one true true).X =
      -((oddFrame 3 K).toHypFrame.longPair fin3_zero_ne_one true false).Y * iBar K := by
  change (iBar K : CliffordAlgebra (quadOdd 3 K)) *
      (ι (quadOdd 3 K) ((oddFrame 3 K).vec 0 true) * ι (quadOdd 3 K) ((oddFrame 3 K).vec 1 true)) =
    -(ι (quadOdd 3 K) ((oddFrame 3 K).vec 1 true) * ι (quadOdd 3 K) ((oddFrame 3 K).vec 0 false)) *
      iBar K
  rw [coe_iBar_mul_vec_mul_vec K (by decide) (by decide) true true (ι_vecMinus₀_mul_e₀ K)
    (ι_vecMinus₀_mul_vec_one K true),
    ι_mul_ι_eq_neg_of_polar_eq_zero _ ((oddFrame 3 K).polar_vec_of_ne (by decide) false true)]

theorem coe_iBar_mul_longPair_true_Y :
    (iBar K : CliffordAlgebra (quadOdd 3 K)) *
        ((oddFrame 3 K).toHypFrame.longPair fin3_zero_ne_one true true).Y =
      -((oddFrame 3 K).toHypFrame.longPair fin3_zero_ne_one true false).X * iBar K := by
  change (iBar K : CliffordAlgebra (quadOdd 3 K)) *
      (ι (quadOdd 3 K) ((oddFrame 3 K).vec 1 false) *
        ι (quadOdd 3 K) ((oddFrame 3 K).vec 0 false)) =
    -(ι (quadOdd 3 K) ((oddFrame 3 K).vec 0 true) * ι (quadOdd 3 K) ((oddFrame 3 K).vec 1 false)) *
      iBar K
  rw [coe_iBar_mul_vec_mul_vec K (by decide) (by decide) false false
    (ι_vecMinus₀_mul_vec_one K false) (ι_vecMinus₀_mul_f₀ K),
    ι_mul_ι_eq_neg_of_polar_eq_zero _ ((oddFrame 3 K).polar_vec_of_ne (by decide) false true)]

theorem coe_iBar_mul_longPair_false_X :
    (iBar K : CliffordAlgebra (quadOdd 3 K)) *
        ((oddFrame 3 K).toHypFrame.longPair fin3_zero_ne_one true false).X =
      -((oddFrame 3 K).toHypFrame.longPair fin3_zero_ne_one true true).Y * iBar K := by
  change (iBar K : CliffordAlgebra (quadOdd 3 K)) *
      (ι (quadOdd 3 K) ((oddFrame 3 K).vec 0 true) * ι (quadOdd 3 K) ((oddFrame 3 K).vec 1 false)) =
    -(ι (quadOdd 3 K) ((oddFrame 3 K).vec 1 false) * ι (quadOdd 3 K) ((oddFrame 3 K).vec 0 false)) *
      iBar K
  rw [coe_iBar_mul_vec_mul_vec K (by decide) (by decide) true false (ι_vecMinus₀_mul_e₀ K)
    (ι_vecMinus₀_mul_vec_one K false),
    ι_mul_ι_eq_neg_of_polar_eq_zero _ ((oddFrame 3 K).polar_vec_of_ne (by decide) false false)]

theorem coe_iBar_mul_longPair_false_Y :
    (iBar K : CliffordAlgebra (quadOdd 3 K)) *
        ((oddFrame 3 K).toHypFrame.longPair fin3_zero_ne_one true false).Y =
      -((oddFrame 3 K).toHypFrame.longPair fin3_zero_ne_one true true).X * iBar K := by
  change (iBar K : CliffordAlgebra (quadOdd 3 K)) *
      (ι (quadOdd 3 K) ((oddFrame 3 K).vec 1 true) * ι (quadOdd 3 K) ((oddFrame 3 K).vec 0 false)) =
    -(ι (quadOdd 3 K) ((oddFrame 3 K).vec 0 true) * ι (quadOdd 3 K) ((oddFrame 3 K).vec 1 true)) *
      iBar K
  rw [coe_iBar_mul_vec_mul_vec K (by decide) (by decide) true false
    (ι_vecMinus₀_mul_vec_one K true) (ι_vecMinus₀_mul_f₀ K),
    ι_mul_ι_eq_neg_of_polar_eq_zero _ ((oddFrame 3 K).polar_vec_of_ne (by decide) true true)]

theorem iBar_mul_longSL2_true (M : SL(2, K)) :
    iBar K * (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true true M =
      (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false (slTwist M) * iBar K := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, Submonoid.coe_mul, HypFrame.coe_longSL2, HypFrame.coe_longSL2,
    coe_slTwist]
  exact SL2Pair.mul_toFun_of_mul_eq _ _ (coe_iBar_mul_longPair_true_X K)
    (coe_iBar_mul_longPair_true_Y K) _

theorem iBar_mul_longSL2_false (M : SL(2, K)) :
    iBar K * (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false M =
      (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true true (slTwist M) * iBar K := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, Submonoid.coe_mul, HypFrame.coe_longSL2, HypFrame.coe_longSL2,
    coe_slTwist]
  exact SL2Pair.mul_toFun_of_mul_eq _ _ (coe_iBar_mul_longPair_false_X K)
    (coe_iBar_mul_longPair_false_Y K) _

theorem iBar_conj_longSL2_true (M : SL(2, K)) :
    iBar K * (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true true M * (iBar K)⁻¹ =
      (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false (slTwist M) := by
  rw [iBar_mul_longSL2_true, mul_inv_cancel_right]

theorem iBar_conj_longSL2_false (M : SL(2, K)) :
    iBar K * (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false M * (iBar K)⁻¹ =
      (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true true (slTwist M) := by
  rw [iBar_mul_longSL2_false, mul_inv_cancel_right]

theorem map_conj_iBar_spinJ₃ :
    (spinJ₃ K).map (MulAut.conj (iBar K)).toMonoidHom = spinJ₂ K := by
  ext y
  constructor
  · rintro ⟨_, ⟨M, rfl⟩, rfl⟩
    refine ⟨slTwist M, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, iBar_conj_longSL2_false]
  · rintro ⟨M, rfl⟩
    refine ⟨_, ⟨slTwist M, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, iBar_conj_longSL2_false, slTwist_slTwist]

theorem iBar_conj_tSeven : iBar K * tSeven K * (iBar K)⁻¹ = spinZ K * tSeven K := by
  have h := iBar_conj_longSL2_true K (-1)
  rw [slTwist_neg_one] at h
  rw [tSeven, h]
  exact longSL2_neg_one_not _ fin3_zero_ne_one (nondegenerate_quadOdd 3 K).ne_zero true true

end CFSG.ComponentClassification.HarrisLit.T1.S74
