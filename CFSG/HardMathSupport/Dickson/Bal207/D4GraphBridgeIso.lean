module

public import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Bridge
public import CFSG.HardMathSupport.Foote.E27.Q2OrthModel

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Bal207.D4Graph

open CFSG.HardMathSupport.Lang.Coordinator.D4Bridge CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped Matrix

section Iso

variable (K : Type) [Field K] [Finite K]


theorem exists_thetaOmega_ne_one : ∃ x, thetaOmega K x ≠ 1 := by
  obtain ⟨c, hc⟩ := exists_ne_one_adjointGroup_D4 K
  obtain ⟨x, rfl⟩ := thetaOmega_surjective K c
  exact ⟨x, hc⟩

theorem ker_thetaOmega :
    (thetaOmega K).ker = (StatedScalars (Fin 4 ⊕ Fin 4) K).subgroupOf
      (StatedOmega (StatedQuadPlus 4 K)) := by
  rw [← center_statedOmega_quadPlus (by norm_num : 3 ≤ 4)]
  refine le_antisymm
    (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
      (isQuasisimple_statedOmega_quadPlus (by norm_num)) (exists_thetaOmega_ne_one K)) ?_
  intro z hz
  rw [MonoidHom.mem_ker]
  have hZ : thetaOmega K z ∈ Subgroup.center (adjointGroup Tag.D4 K) := by
    rw [Subgroup.mem_center_iff]
    intro c
    obtain ⟨y, rfl⟩ := thetaOmega_surjective K c
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz y).symm]
  rw [center_adjointGroup_eq_bot] at hZ
  exact hZ

@[expose] def isoAdj :
    StatedProj (StatedOmega (StatedQuadPlus 4 K)) ≃* adjointGroup Tag.D4 K :=
  MulEquiv.ofBijective
    (QuotientGroup.lift _ (thetaOmega K) (ker_thetaOmega K).symm.le)
    ⟨(injective_iff_map_eq_one _).2 fun q hq => by
      induction q using QuotientGroup.induction_on with
      | H x =>
        rw [QuotientGroup.lift_mk] at hq
        exact (QuotientGroup.eq_one_iff x).2 ((ker_thetaOmega K).le hq),
     fun c => by
      obtain ⟨x, rfl⟩ := thetaOmega_surjective K c
      exact ⟨QuotientGroup.mk x, QuotientGroup.lift_mk _ _ x⟩⟩

theorem isoAdj_mk (x : StatedOmega (StatedQuadPlus 4 K)) :
    isoAdj K (QuotientGroup.mk x) = thetaOmega K x :=
  rfl

end Iso

section Sigma

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem statedQuadPlus_map (v : Fin 4 ⊕ Fin 4 → K) :
    StatedQuadPlus 4 K (fun i => σ (v i)) = σ (StatedQuadPlus 4 K v) := by
  simp [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, map_sum]

@[expose] def sigmaOmega :
    StatedOmega (StatedQuadPlus 4 K) ≃* StatedOmega (StatedQuadPlus 4 K) :=
  (MulEquiv.subgroupMap (CFSG.HardMathSupport.Foote.E27.Q2.glMap σ)
    (StatedOmega (StatedQuadPlus 4 K))).trans
    (MulEquiv.subgroupCongr (CFSG.HardMathSupport.Foote.E27.Q2.glMap_statedOmega σ _ _
      (statedQuadPlus_map σ)))

theorem val_sigmaOmega (A : StatedOmega (StatedQuadPlus 4 K)) :
    (((sigmaOmega σ A : StatedOmega (StatedQuadPlus 4 K)) :
        Matrix.GeneralLinearGroup (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) =
      ((A : Matrix.GeneralLinearGroup (Fin 4 ⊕ Fin 4) K) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K).map σ := rfl

theorem omegaEquiv_apply (A : StatedOmega (StatedQuadPlus 4 K)) (v : V K) :
    ((omegaEquiv K A : elementaryGroup (quadPlus 4 K)) : V K ≃ₗ[K] V K) v =
      ((A : Matrix.GeneralLinearGroup (Fin 4 ⊕ Fin 4) K) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v := rfl

theorem omegaEquiv_sigmaOmega_apply (A : StatedOmega (StatedQuadPlus 4 K)) (v : V K) :
    ((omegaEquiv K (sigmaOmega σ A) : elementaryGroup (quadPlus 4 K)) : V K ≃ₗ[K] V K)
        (fun i => σ (v i)) =
      fun i => σ (((omegaEquiv K A : elementaryGroup (quadPlus 4 K)) : V K ≃ₗ[K] V K) v i) := by
  rw [omegaEquiv_apply, omegaEquiv_apply, val_sigmaOmega]
  exact CFSG.HardMathSupport.Foote.E27.Q2.mulVec_map_comp σ _ v

theorem quadPlus_map (v : V K) :
    quadPlus 4 K (fun i => σ (v i)) = σ (quadPlus 4 K v) := by
  have h := statedQuadPlus_map σ v
  rwa [← coe_quadPlus 4 K] at h

theorem polar_quadPlus_map (x y : V K) :
    polar (quadPlus 4 K) (fun i => σ (x i)) (fun i => σ (y i)) = σ (polar (quadPlus 4 K) x y) := by
  have h : (fun i => σ ((x + y) i)) = (fun i => σ (x i)) + (fun i => σ (y i)) := by
    funext i
    simp
  rw [polar, polar, ← h, quadPlus_map, quadPlus_map, quadPlus_map, map_sub, map_sub]

theorem sigma_eichler {u w : V K} (hu : quadPlus 4 K u = 0) (huw : polar (quadPlus 4 K) u w = 0)
    (x : V K) :
    (fun i => σ (eichler (quadPlus 4 K) u w x i)) =
      eichler (quadPlus 4 K) (fun i => σ (u i)) (fun i => σ (w i)) (fun i => σ (x i)) := by
  have hu' : quadPlus 4 K (fun i => σ (u i)) = 0 := by rw [quadPlus_map, hu, map_zero]
  have huw' : polar (quadPlus 4 K) (fun i => σ (u i)) (fun i => σ (w i)) = 0 := by
    rw [polar_quadPlus_map, huw, map_zero]
  rw [eichler_apply hu huw, eichler_apply hu' huw']
  funext i
  simp [polar_quadPlus_map, quadPlus_map, map_sub, map_add, map_mul]

end Sigma

end CFSG.HardMathSupport.Dickson.Bal207.D4Graph

end
