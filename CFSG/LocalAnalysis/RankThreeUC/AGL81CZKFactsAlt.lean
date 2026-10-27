module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CInputs
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

theorem kFactAutA11_holds : KFactAutA11 := by
  have hb := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 11
    (by norm_num) (by norm_num)
  have hcard : Nat.card (MulAut (alternatingGroup (Fin 11))) = Nat.card (Equiv.Perm (Fin 11)) :=
    (Nat.card_congr (Equiv.ofBijective _ hb)).symm
  rw [KFactAutA11, hcard, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

theorem kFactThreeRankA11_holds : KFactThreeRankA11 := by
  rw [KFactThreeRankA11, CFSG.SectionRank.pRank_coe_eq_openPRank]
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top
    (CFSG.SectionRank.isElemAbelian_sylowThreeAlt (n := 11) (by norm_num))
    (CFSG.SectionRank.card_sylowThreeAlt (n := 11) (by norm_num))

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
