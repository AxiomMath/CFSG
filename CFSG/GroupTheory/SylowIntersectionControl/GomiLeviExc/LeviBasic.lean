module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabLevi

public section

namespace CFSG.GroupTheory.GomiLeviExc

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.AGLEmbeddingD2.ParabLevi

variable {K : Type} [Group K] (D : UniversalRootDatum K)

theorem leviM_coe_finset (J : Finset (Fin D.rank)) : leviM D ↑J = levi D.rootGroup J :=
  rfl

theorem leviM_pair (i j : Fin D.rank) :
    leviM D {i, j} = rankOne D.rootGroup i ⊔ rankOne D.rootGroup j := by
  rw [leviM, iSup_insert, iSup_singleton]

end CFSG.GroupTheory.GomiLeviExc
