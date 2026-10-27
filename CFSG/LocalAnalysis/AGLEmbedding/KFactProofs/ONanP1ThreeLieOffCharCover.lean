module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharEx
public import CFSG.LieType.SeitzGeneration.SpAnisoFinal
public import CFSG.LieType.SeitzGeneration.UnitaryHyperNonsplit
public import CFSG.LieType.SeitzGeneration.OrthHyperExB3
public import CFSG.LieType.SeitzGeneration.HyperExExcV2
public import CFSG.LieType.SeitzGeneration.HyperExCubeTw
public import CFSG.LieType.SeitzGeneration.HyperExCubeLevi
public import CFSG.LieType.SeitzGeneration.HyperCoverE6
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGenAt
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentOffCharAut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffChar
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLK0ThreeKill
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

theorem hyperGen_map_subtype {p : ℕ} {Y : Type*} [Group Y] {K : Subgroup Y} {E : Subgroup K}
    (h : HyperGen p (⊤ : Subgroup K) E) : HyperGen p K (E.map K.subtype) := by
  intro y hy
  have hmem := h (Subgroup.mem_top (⟨y, hy⟩ : K))
  have hle : (Subgroup.closure {k : K | k ∈ (⊤ : Subgroup K) ∧ ∃ F : Subgroup K, F ≤ E ∧
      F.relIndex E = p ∧ ∀ f ∈ F, f * k = k * f}).map K.subtype ≤
      Subgroup.closure {k : Y | k ∈ K ∧ ∃ F : Subgroup Y, F ≤ E.map K.subtype ∧
        F.relIndex (E.map K.subtype) = p ∧ ∀ f ∈ F, f * k = k * f} := by
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨k, ⟨-, F, hFE, hFi, hF⟩, rfl⟩
    refine ⟨k.2, F.map K.subtype, Subgroup.map_mono hFE, ?_, ?_⟩
    · rw [Subgroup.relIndex_map_map_of_injective _ _ K.subtype_injective]
      exact hFi
    · rintro _ ⟨f, hf, rfl⟩
      exact congrArg Subtype.val (hF f hf)
  exact hle ⟨⟨y, hy⟩, hmem, rfl⟩

end CFSG.AGLEmbedding
