module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Quasithin CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {X : Type} [Group X]

theorem escape_of_le_gnImg {T K C₁ C₂ : Subgroup X} {W : Subgroup (X ⧸ gnC T)}
    (hW : W ≤ gnImg T K) (h : C₁ ≤ centerOf K ∨ K ≤ Subgroup.normalizer (C₂ : Set X)) :
    W ≤ gnImg T (Subgroup.centralizer (C₁ : Set X)) ∨
      W ≤ gnImg T (Subgroup.normalizer (C₂ : Set X)) := by
  rcases h with h1 | h2
  · refine Or.inl (hW.trans (Subgroup.map_mono fun k hk => ?_))
    exact Subgroup.mem_centralizer_iff.2 fun c hc =>
      (Subgroup.mem_centralizer_iff.1 (h1 hc).2 k hk).symm
  · exact Or.inr (hW.trans (Subgroup.map_mono h2))

end CFSG.AGLEmbeddingD2.Tits.GN516
