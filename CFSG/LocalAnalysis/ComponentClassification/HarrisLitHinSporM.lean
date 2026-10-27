module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSpor
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBMSpor

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.RestrictedStd.Spor

theorem hinFor_spor_M
    : HinFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .M := by
  refine hinFor_of_comps_simple (fun G _ _ hGs _ ⟨eG⟩ t ht B hB hsB => ?_)
    (fun G _ _ hs _ hG α _ hα => ?_)
  · obtain ⟨h41, -⟩ := CatLeafProof.monsterLocalComponentsInput G hGs ⟨eG⟩ t ht B hB
    obtain ⟨eM⟩ := RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple eG
    have hM : Nat.card (↥B ⧸ center ↥B) ∣ Open.monsterOrder := by
      rw [← YGroups.Y443.natCard_Gmat_eq_monsterOrder, ← Nat.card_congr eM.toEquiv]
      exact (Subgroup.card_quotient_dvd_card _).trans ((Subgroup.card_subgroup_dvd_card B).trans
        (Subgroup.card_subgroup_dvd_card _))
    exact GSThmB.MonsterArith.not_smallCentralQuotient h41 hM hsB
  · exact (hα (CatLeafProof.monsterInnerInput G hs hG α)).elim

end CFSG.ComponentClassification.HarrisLit.Hin
