module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbEdgeLevi
public import CFSG.Timmesfeld.ARS.LinearLevis

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.Fam

theorem edgeCond_sl {m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (H : Fin (CFSG.LieType.Universal.SpecialLinear.rootDatum m F).rank →
      Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (hrank : 3 ≤ (CFSG.LieType.Universal.SpecialLinear.rootDatum m F).rank)
    (u v : Fin (CFSG.LieType.Universal.SpecialLinear.rootDatum m F).rank)
    (hadj : (TauCeti.diagramGraph
      (CFSG.LieType.Universal.SpecialLinear.rootDatum m F).cartan).Adj u v) :
    CFSG.AGLEmbeddingD2.Tits.GN516.Core.EdgeCond
      (CFSG.LieType.Universal.SpecialLinear.rootDatum m F) H u v := by
  have hL := CFSG.Timmesfeld.ARS.simplyLacedLevis_specialLinear m F
  have hpath : (SimpleGraph.pathGraph m).Adj u v := by
    have h : (TauCeti.diagramGraph (CartanMatrix.A m)).Adj u v := hadj
    rwa [TauCeti.DynkinType.diagramGraph_cartanMatrix_A] at h
  refine Or.inl ?_
  rcases SimpleGraph.pathGraph_adj.1 hpath with h | h
  · exact CFSG.AGLEmbeddingD2.Tits.GN516.EdgeLev.edgeLevi_of_simplyLacedLevis hL h.symm
  · exact CFSG.AGLEmbeddingD2.Tits.GN516.EdgeLev.edgeLevi_symm
      (CFSG.AGLEmbeddingD2.Tits.GN516.EdgeLev.edgeLevi_of_simplyLacedLevis hL h.symm)

end CFSG.AGLEmbeddingD2.Tits.GN516.Fam
