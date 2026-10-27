module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXC6NoSix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXC6L33
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXC6U33

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Blueprint


theorem l34g_c6_of_smallF3Star {Y : Type} [Group Y] (h : SmallF3StarQuotient Y) : L34GC6 Y := by
  rcases h with h | h | h | h
  · exact l34g_c6_of_lieModel_psl2_char3 h
  · exact l34g_c6_of_lieModel_psl2_char3 h
  · exact l34g_c6_L33 h
  · exact l34g_c6_U33 h

theorem l34g_hard_scope {Y : Type} [Group Y] (hY : L34GStarQuotient Y) (hC : ¬ L34GC6 Y) :
    SmallF3OmegaQuotient Y ∨ (CFSG.IsQuasisimple Y ∧ IsTwoU43 Y) := by
  rcases hY with (h | h) | h
  · exact Or.inl h
  · exact absurd (l34g_c6_of_smallF3Star h) hC
  · exact Or.inr h

end CFSG.OddStandard.SmallF3.Omega
