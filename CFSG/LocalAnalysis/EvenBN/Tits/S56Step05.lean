module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Steps
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P05Core
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P05Ctr
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P05Syl

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

section Step05


theorem step05_holds : Step05 := by
  intro G _ _ d z₀ h49 hd hz
  obtain ⟨c1, c2, c6, c7, c8, c9, c10, c11⟩ := node05_core h49 hd hz
  obtain ⟨c3, c4, c5⟩ := node05_index_sylow h49 hd
  obtain ⟨c12, c13⟩ := node05_center h49 hd hz
  exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩

end Step05

end CFSG.LocalAnalysis.EvenBN.Tits.N
