module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CentDMat
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Om6ParG
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGAutCentBK

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {t : OGroup Q} (D : Om6Par Q t)

theorem sec5cd_scalar_W {x : simGroup Q}
    (hL : ∀ a : SL2F3, a ^ 4 = 1 →
      simAct Q x (D.theta (leftMulHom a)) = D.theta (leftMulHom a))
    (hR : ∀ b : SL2F3, b ^ 4 = 1 →
      simAct Q x (D.theta (rightMulHom b)) = D.theta (rightMulHom b)) :
    simAct Q x t = t ∧ ∃ c : ZMod 3, c ≠ 0 ∧ ∀ X : Mat2,
      (x : V ≃ₗ[ZMod 3] V) (D.iota X) = c • D.iota X := by
  have hxt : simAct Q x t = t := by
    have h := hL sl2f3NegOne (by decide +kernel)
    rwa [leftMulHom_eq_piOrth coe_sl2f3NegOne, D.theta_piOrth] at h
  refine ⟨hxt, ?_⟩
  obtain ⟨σ, hσ⟩ := D.exists_sigma hxt
  have hσL : ∀ A : SL2F3, A ^ 4 = 1 → ∀ X : Mat2, σ ((A : Mat2) * X) = (A : Mat2) * σ X := by
    intro A hA X
    apply D.iota_injective
    have e1 : (x : V ≃ₗ[ZMod 3] V) (((D.theta (leftMulHom A) : OGroup Q) : V ≃ₗ[ZMod 3] V)
        (D.iota X)) = D.iota (σ ((A : Mat2) * X)) := by
      rw [D.theta_apply_W, leftMulHom_apply, hσ]
    have e2 : ((D.theta (leftMulHom A) : OGroup Q) : V ≃ₗ[ZMod 3] V)
        ((x : V ≃ₗ[ZMod 3] V) (D.iota X)) = D.iota ((A : Mat2) * σ X) := by
      rw [hσ, D.theta_apply_W, leftMulHom_apply]
    rw [← e1, ← e2, om6par_simAct_apply x, hL A hA]
  have hσR : ∀ A : SL2F3, A ^ 4 = 1 → ∀ X : Mat2, σ (X * (A : Mat2)) = σ X * (A : Mat2) := by
    intro A hA X
    have hb : (A⁻¹) ^ 4 = 1 := by rw [inv_pow, hA, inv_one]
    apply D.iota_injective
    have e1 : (x : V ≃ₗ[ZMod 3] V) (((D.theta (rightMulHom A⁻¹) : OGroup Q) : V ≃ₗ[ZMod 3] V)
        (D.iota X)) = D.iota (σ (X * (A : Mat2))) := by
      rw [D.theta_apply_W, rightMulHom_apply, inv_inv, hσ]
    have e2 : ((D.theta (rightMulHom A⁻¹) : OGroup Q) : V ≃ₗ[ZMod 3] V)
        ((x : V ≃ₗ[ZMod 3] V) (D.iota X)) = D.iota (σ X * (A : Mat2)) := by
      rw [hσ, D.theta_apply_W, rightMulHom_apply, inv_inv]
    rw [← e1, ← e2, om6par_simAct_apply x, hR A⁻¹ hb]
  obtain ⟨c, hc⟩ := sec5cd_mat_scalar σ.toLinearMap hσL hσR
  have hxw : ∀ X : Mat2, (x : V ≃ₗ[ZMod 3] V) (D.iota X) = c • D.iota X := fun X => by
    rw [hσ]
    have h := hc X
    simp only [LinearEquiv.coe_coe] at h
    rw [h, map_smul]
  refine ⟨c, ?_, hxw⟩
  rintro rfl
  have h1 := hxw 1
  rw [zero_smul] at h1
  have h2 : D.iota 1 = 0 := (x : V ≃ₗ[ZMod 3] V).injective (by rw [h1, map_zero])
  exact one_ne_zero (D.iota_injective (h2.trans (map_zero D.iota).symm))

theorem sec5cd_core {x : simGroup Q}
    (hL : ∀ a : SL2F3, a ^ 4 = 1 →
      simAct Q x (D.theta (leftMulHom a)) = D.theta (leftMulHom a))
    (hR : ∀ b : SL2F3, b ^ 4 = 1 →
      simAct Q x (D.theta (rightMulHom b)) = D.theta (rightMulHom b)) :
    ∃ b : OGroup (Q.restrict (FGSplit.comm D.nd D.htt).P),
      (QuotientGroup.mk x : ProjSim Q) = fgIotaP (FGSplit.comm D.nd D.htt) b := by
  obtain ⟨hxt, c, hc0, hxw⟩ := sec5cd_scalar_W D hL hR
  have hc1 : c = 1 ∨ c = -1 := by
    revert hc0
    generalize c = c'
    revert c'
    decide
  have hcw : ∀ w ∈ (FGSplit.comm D.nd D.htt).W, (x : V ≃ₗ[ZMod 3] V) w = c • w := by
    intro w hw
    obtain ⟨X, hX⟩ := D.e.toLinearEquiv.surjective (⟨w, hw⟩ : commSp t)
    have hX' : D.iota X = w := congrArg Subtype.val hX
    rw [← hX', hxw]
  have hP : ∀ p ∈ (FGSplit.comm D.nd D.htt).P, (x : V ≃ₗ[ZMod 3] V) p ∈
      (FGSplit.comm D.nd D.htt).P := om6par_preserve_P hxt
  have h3 : 3 ≤ Module.finrank (ZMod 3) (FGSplit.comm D.nd D.htt).W := by
    show 3 ≤ Module.finrank (ZMod 3) (commSp t)
    rw [D.dimW]
    norm_num
  have hO := fg_bk_orthogonal (FGSplit.comm D.nd D.htt) h3 x hc1 hcw
  let g₀ : OGroup Q := ⟨(x : V ≃ₗ[ZMod 3] V), hO⟩
  have hg₀ : (QuotientGroup.mk x : ProjSim Q) = projOrthToProjSim Q (toProj Q g₀) := rfl
  rcases hc1 with rfl | rfl
  · obtain ⟨b, hb⟩ := (FGSplit.comm D.nd D.htt).ext_surj g₀
      (fun w => by simpa using hcw w w.2) (fun p => hP p p.2)
    refine ⟨b, ?_⟩
    rw [hg₀, fgIotaP, MonoidHom.comp_apply, MonoidHom.comp_apply, hb]
  · let g₁ : OGroup Q := piOrth Q * g₀
    obtain ⟨b, hb⟩ := (FGSplit.comm D.nd D.htt).ext_surj g₁
      (fun w => by
        change (piOrth Q : V ≃ₗ[ZMod 3] V) ((x : V ≃ₗ[ZMod 3] V) (w : V)) = (w : V)
        rw [coe_piOrth_apply, hcw w w.2]
        simp)
      (fun p => by
        change (piOrth Q : V ≃ₗ[ZMod 3] V) ((x : V ≃ₗ[ZMod 3] V) (p : V)) ∈
          (FGSplit.comm D.nd D.htt).P
        rw [coe_piOrth_apply]
        exact (FGSplit.comm D.nd D.htt).P.neg_mem (hP p p.2))
    refine ⟨b, ?_⟩
    rw [hg₀, fgIotaP, MonoidHom.comp_apply, MonoidHom.comp_apply, hb]
    congr 1
    rw [show g₁ = piOrth Q * g₀ from rfl, map_mul, toProj_piOrth, one_mul]

end CFSG.OddStandard.SmallF3.Omega
