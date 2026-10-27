module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15PerMaxSup

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def K54InnerAt {X : Type} [Group X] [Finite X] (T : Subgroup X)
    (Ls : Subgroup (X ⧸ gnC T)) : Prop :=
  ∀ A : Subgroup X, IsMaxElemAbelian T A →
    gnImg T A ≤ Ls ⊔ Subgroup.centralizer (Ls : Set (X ⧸ gnC T))

theorem gnImg_thompsonJ_le_sup_centralizer_of_K54InnerAt {X : Type} [Group X] [Finite X]
    {T : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} (h : K54InnerAt T Ls) :
    gnImg T (thompsonJ T) ≤ Ls ⊔ Subgroup.centralizer (Ls : Set (X ⧸ gnC T)) :=
  gnImg_thompsonJ_le_sup_centralizer_of_perMaxSup h

end CFSG.LocalAnalysis.RankThreeUC.S15

end
