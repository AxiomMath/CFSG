module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OrthBlocks
public import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Bridge

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2

open CFSG.HardMathSupport.Lang.Coordinator.D4Bridge CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank CFSG.Open CFSG.RankThree.Classical2

variable (K : Type) [Field K] [Finite K]

section Proj


theorem ker_thetaOmega :
    (thetaOmega K).ker = Subgroup.center (StatedOmega (StatedQuadPlus 4 K)) := by
  have hK : CFSG.IsQuasisimple (StatedOmega (StatedQuadPlus 4 K)) :=
    isQuasisimple_statedOmega_quadPlus (by norm_num)
  apply le_antisymm
  · obtain ⟨c, hc⟩ := exists_ne_one_adjointGroup_D4 K
    obtain ⟨x, rfl⟩ := thetaOmega_surjective K c
    exact CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hK ⟨x, hc⟩
  · intro z hz
    rw [MonoidHom.mem_ker]
    have h : thetaOmega K z ∈ Subgroup.center (adjointGroup Tag.D4 K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨w, rfl⟩ := thetaOmega_surjective K g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz w]
    rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at h
    exact h

@[expose] noncomputable def eP : StatedProj (StatedOmega (StatedQuadPlus 4 K)) ≃* adjointGroup Tag.D4 K :=
  MulEquiv.ofBijective
    (QuotientGroup.lift ((StatedScalars _ K).subgroupOf (StatedOmega (StatedQuadPlus 4 K)))
      (thetaOmega K) (fun z hz => by
        have : z ∈ Subgroup.center (StatedOmega (StatedQuadPlus 4 K)) := by
          rw [center_statedOmega_quadPlus (by norm_num)]
          exact hz
        rw [← ker_thetaOmega] at this
        exact this))
    ⟨by
      rw [injective_iff_map_eq_one]
      intro q hq
      induction q using QuotientGroup.induction_on with
      | H z =>
        rw [QuotientGroup.lift_mk] at hq
        rw [QuotientGroup.eq_one_iff]
        have : z ∈ (thetaOmega K).ker := hq
        rw [ker_thetaOmega, center_statedOmega_quadPlus (by norm_num)] at this
        exact this,
     by
      intro c
      obtain ⟨z, rfl⟩ := thetaOmega_surjective K c
      exact ⟨QuotientGroup.mk z, QuotientGroup.lift_mk _ _ _⟩⟩

theorem eP_mk (A : StatedOmega (StatedQuadPlus 4 K)) :
    eP K (QuotientGroup.mk A) = thetaOmega K A := rfl

@[expose] noncomputable def eTheta : ProjOrthDerived (quadPlus 4 K) ≃* adjointGroup Tag.D4 K :=
  (CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.projOrthEquiv (coe_quadPlus 4 K)).symm.trans (eP K)

theorem eTheta_mk (A : StatedOmega (StatedQuadPlus 4 K)) :
    eTheta K (QuotientGroup.mk (CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.omegaOrthEquiv
      (coe_quadPlus 4 K) A)) = thetaOmega K A := by
  rw [eTheta, MulEquiv.trans_apply]
  have h : (CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.projOrthEquiv (coe_quadPlus 4 K)).symm
      (QuotientGroup.mk (CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.omegaOrthEquiv
        (coe_quadPlus 4 K) A)) = QuotientGroup.mk A := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [h, eP_mk]

end Proj

end CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2
