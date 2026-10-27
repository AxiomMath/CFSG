module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharOutTower

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzNonNormal

open CFSG.AGLEmbedding

theorem outTowerAt_of_commutator_mem_inner {K : Type*} [Group K] {p : ℕ}
    (h : ∀ γ α : MulAut K, γ * α * γ⁻¹ * α⁻¹ ∈ (MulAut.conj : K →* MulAut K).range) :
    CFSG.AGLEmbedding.OutTowerAt K p := by
  have hN : ((MulAut.conj : K →* MulAut K).range).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal K
  refine ⟨(MulAut.conj : K →* MulAut K).range, fun γ α _ => h γ α, fun α _ δ hδ => ?_⟩
  have hαδ : α * δ * α⁻¹ ∈ (MulAut.conj : K →* MulAut K).range := hN.conj_mem δ hδ α
  exact Subgroup.mul_mem _ hαδ (Subgroup.inv_mem _ hδ)

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzNonNormal

end
