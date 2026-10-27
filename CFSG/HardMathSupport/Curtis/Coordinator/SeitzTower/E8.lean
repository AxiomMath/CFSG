module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.Abelian
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.ExcE
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzNonNormal.E8Diag

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.AGLEmbedding TauCeti
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section


theorem outerComm_adjoint_E8 (K : Type) [Field K] [Finite K] :
    OuterComm (adjointGroup .E8 K) := by
  refine outerComm_of_normalForm {θ | ∃ σ : K ≃+* K, θ = exactNormalAut .E8 K 1 σ 0} ?_ ?_
  · rintro _ ⟨σ, rfl⟩ _ ⟨σ', rfl⟩
    rw [exactNormalAut_one_zero_mul, exactNormalAut_one_zero_mul,
      SeitzNonNormal.ringEquiv_mul_comm_of_finite]
  · intro α
    obtain ⟨x, hx, σ, hσ⟩ := SeitzNonNormal.exists_E8_normal_form K α
    refine ⟨⟨x, hx⟩, exactNormalAut .E8 K 1 σ 0, ⟨σ, rfl⟩, MulEquiv.ext fun h => Subtype.ext ?_⟩
    rw [hσ h, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_exactNormalAut_zero, rootDiagUnit_one, one_mul, inv_one, mul_one]

theorem p1OffCharAlmostSimpleNonNormalAt_E8 {q : PrimePower} (hv : (LieTypeIndex.E8 q).Valid) :
    P1OffCharAlmostSimpleNonNormalAt ⟨.E8 q, hv⟩ := by
  obtain ⟨F, _, _, ⟨e⟩⟩ := exists_mulEquiv_adjoint
    (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).e8 q hv
  exact p1OffCharAlmostSimpleNonNormalAt_of_outerComm (OuterComm.of_mulEquiv e
    (outerComm_adjoint_E8 F))

end

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower
