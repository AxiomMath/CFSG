module

public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpA10Comps
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofMonster
public import CFSG.Monster.SteinbergMSporadicOddCoreFree

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup CFSG.Blueprint

theorem a10SporClause_M :
    A10SporClauseFor .M :=
  a10SporClauseFor_of_comps CatalogueU.sporadicOddCoreFree_M
    (fun G _ _ hs _ hG t ht K hK hc => by
      obtain ⟨h41, -⟩ := CatLeafProof.monsterLocalComponentsInput G hs hG t ht K hK
      rw [hc] at h41
      exact absurd h41 (by decide))
    (fun G _ _ hs _ hG α _ hα => absurd (CatLeafProof.monsterInnerInput G hs hG α) hα)

end CFSG.ComponentClassification.EvenPump
