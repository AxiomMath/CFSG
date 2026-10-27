module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedAltSevenCertificate
public import CFSG.Sporadic.Schreier.LyCover
public import Certificates.Certificate3085

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedAltSeven

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native

theorem cStar_eight_mul_self : cStar 8 * cStar 8 = lyz := by
  have h := UnbalancedAltSeven.Native.lift_square_certificate
  unfold UnbalancedAltSeven.Native.liftSquareCheck at h
  simp only [beq_iff_eq] at h
  rw [← csArr_def] at h
  have e := congrArg (toMat 5 111) h
  rw [toMat_mulM, (repM_csArr 8).1, toMat_matA] at e
  apply mat_injective
  rw [mat_mul, e, lyz, mat_a]

theorem pPerm_eight : pPerm 8 = Equiv.swap 6 7 * Equiv.swap 8 10 := by decide +kernel

theorem ly_double_transposition_lift_square :
    cStar 8 ^ 2 = lyz ∧ pPerm 8 = Equiv.swap 6 7 * Equiv.swap 8 10 ∧
      ∀ x : Fin 11, pStar 8 x = (Equiv.swap 6 7 * Equiv.swap 8 10 : Equiv.Perm (Fin 11)) x := by
  refine ⟨by rw [sq, cStar_eight_mul_self], pPerm_eight, fun x => ?_⟩
  rw [← pPerm_eight, pPerm_apply (by norm_num)]

end CFSG.ComponentClassification.UnbalancedAltSeven
