module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement

@[expose] def JOutCentralAt {X : Type} [Group X] [Finite X] (T : Subgroup X) : Prop :=
  ∀ L : Subgroup (X ⧸ gnC T), IsComponentOf L ⊤ → ⁅L, gnImg T (thompsonJ T)⁆ ≠ ⊥ →
    ¬ IsMulCommutative (Outer ↥L) →
    ∀ w ∈ Subgroup.normalizer (L : Set (X ⧸ gnC T)), ∀ j ∈ gnImg T (thompsonJ T),
      ⁅w, j⁆ ∈ L ⊔ Subgroup.centralizer (L : Set (X ⧸ gnC T))

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15

end
