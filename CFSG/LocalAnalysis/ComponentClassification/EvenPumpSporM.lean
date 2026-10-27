module

public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpSporBasic
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpSporM

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG.ComponentClassification.SolMax
open CFSG Subgroup CFSG.Blueprint

theorem evenPumpSpor_M :
    EvenPumpSporClauseFor .M :=
  evenPumpSporClauseFor_of_comps CatalogueU.sporadicOddCoreFree_M
    (fun G _ _ hs _ ⟨e⟩ t ht B hB => by
      obtain ⟨E⟩ := RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
      have hG : Nat.card G = Open.monsterOrder := by
        rw [Nat.card_congr E.toEquiv, YGroups.Y443.natCard_Gmat_eq_monsterOrder]
      obtain ⟨h41, -⟩ := CatLeafProof.monsterLocalComponentsInput G hs ⟨e⟩ t ht B hB
      refine noEvenAltBelow_of_card_quotient_center fun m _ hm7 hmN h => ?_
      rw [h] at h41
      exact not_two_pow_dvd_of_le_monsterOrder (by omega) (hG ▸ hmN) h41)
    (fun G _ _ hs _ hG α _ hα => absurd (CatLeafProof.monsterInnerInput G hs hG α) hα)

end CFSG.ComponentClassification.EvenPump
