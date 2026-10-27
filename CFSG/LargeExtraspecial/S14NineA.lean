module

public import CFSG.LargeExtraspecial.S14Early
public import CFSG.LargeExtraspecial.S9RBMain
public import CFSG.LargeExtraspecial.S9RCMain
public import CFSG.LargeExtraspecial.S14Claims

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open CFSG.LargeExtraspecial.S4

theorem s9a6pglStmt_of (hCE : CentralExtInput.{0}) : S9A6PGLStmt := by
  intro G _ _ _ S g t hSt H C ht ht1 hVQ h
  have hNo : NoA2 S g := noA2_of (hSt.noA2 g H.conj_mem H.conj_ne)
  rcases h with h | h
  · exact S9.timmesfeld_9_2_full hCE (irr_of_not_isReducible hSt.irr) H hNo C ht ht1 hVQ
      hSt.abar_ne h
  · exact S10.noPGL25 S g H hNo C ht ht1 hVQ hSt.rbar_ne hSt.abar_ne h

end CFSG.LargeExtraspecial.S14
