module

public import CFSG.LocalAnalysis.RankThreeUC.ModuleHypotheses
import all CFSG.LocalAnalysis.RankThreeUC.ModuleHypotheses

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.CentralizerOnQuotientMembership

theorem mem_centralizerOnQuotient {G : Type} [Group G] {M V₀ V : Subgroup G} {g : G} :
    g ∈ CFSG.LocalAnalysis.RankThreeUC.centralizerOnQuotient M V₀ V ↔ g ∈ M ∧ g ∈ Subgroup.normalizer (V : Set G) ∧
      g ∈ Subgroup.normalizer (V₀ : Set G) ∧ ∀ v ∈ V, g * v * g⁻¹ * v⁻¹ ∈ V₀ := by
  unfold CFSG.LocalAnalysis.RankThreeUC.centralizerOnQuotient
  exact Iff.rfl

end CFSG.GroupTheory.CoprimeActionSupport.CentralizerOnQuotientMembership
