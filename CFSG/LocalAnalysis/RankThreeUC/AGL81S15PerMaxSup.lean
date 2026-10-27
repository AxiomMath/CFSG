module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open Pointwise

theorem gnImg_thompsonJ_le_sup_centralizer_of_perMaxSup
    {X : Type} [Group X] [Finite X] {T : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hA : ∀ A : Subgroup X, IsMaxElemAbelian T A →
      gnImg T A ≤ Ls ⊔ Subgroup.centralizer (Ls : Set (X ⧸ gnC T))) :
    gnImg T (thompsonJ T) ≤ Ls ⊔ Subgroup.centralizer (Ls : Set (X ⧸ gnC T)) := by
  unfold thompsonJ
  conv_lhs => simp only [gnImg, Subgroup.map_iSup]
  refine iSup_le (fun A => ?_)
  exact iSup_le (fun hAmax => hA A hAmax)

end CFSG.LocalAnalysis.RankThreeUC.S15

end
