module

public import CFSG.LocalAnalysis.ComponentClassification.HeldBalStatements
public import CFSG.LocalAnalysis.OddStandard.ChildHeHeldEnd
import CFSG.LocalAnalysis.OddStandard.Glue
import CFSG.LocalAnalysis.OddStandard.GlueAlt
public import CFSG.LocalAnalysis.OddStandard.ChildHe

public section

namespace CFSG.ComponentClassification.GrSLit

open Subgroup CFSG.OddStandard

theorem heStandardBalanced_of_heldEndStepBal (hE : HeldEndStepBal) : HeStandardBalanced := by
  intro G _ _ _ hnonab hK hU hbal L hL hHe hZ hrank
  obtain ⟨t, htC, ht⟩ := exists_involution_of_standard hL
  obtain ⟨hLT, hcomp⟩ :=
    isPComponent_two_of_standard hL htC ht (even_iff_two_dvd.1 (even_card_of_standard hL))
  have hset : HeldSetting G L :=
    ⟨inferInstance, hnonab, hK, hU, locallyTwoBalanced_of_balanced hbal, ⟨t, ht, hLT, hcomp⟩,
      quotient_pPrimeCore_equiv_he hL hZ hHe⟩
  exact hE G L hset hbal (fun A _ _ => wGroup_eq_bot_of_balanced hbal A)
    (GlueAlt.isStandardSubgroup_of_standardComponentIsStandard hL)
    (nonempty_mulEquiv_he_of_center_eq_bot hZ hHe) (pRank_centralizer_eq_one_of_standard hL hrank)

end CFSG.ComponentClassification.GrSLit
