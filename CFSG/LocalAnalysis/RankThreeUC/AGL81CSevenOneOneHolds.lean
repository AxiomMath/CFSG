module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenOne
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogSchreier
import CFSG.LargeExtraspecial.S8CBFOut

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

theorem sevenOneOne_holds :
    SevenOneOne := by
  intro X _ _ hX L hL hLnorm
  haveI : L.Normal := hLnorm
  let S := ↥L ⧸ center ↥L
  haveI hSsimple : IsSimpleGroup S := hL.1.2.1
  have hnonab : ∃ a b : S, a * b ≠ b * a := hL.1.2.2
  have hcat : CFSG.Open.IsCatalogGroup S :=
    CFSG.Open.IsKGroup.isCatalogGroup_of_surjective hX L hnonab
      (QuotientGroup.mk' (center ↥L)) (QuotientGroup.mk'_surjective (center ↥L))
  have hsol : Group.IsSolvable
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) :=
    CFSG.AGLEmbedding.kFactCatalogSchreier_holds S hSsimple hnonab hcat
  exact CFSG.LargeExtraspecial.S8.exists_derivedSeries_le_sup_centralizer L
    (Subgroup.isPerfect_iff.mp hL.1.1) hsol

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
