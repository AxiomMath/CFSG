module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Row1512Facts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KParU5Holds

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.LocalAnalysis.RankThreeUC.S15

theorem KParU7_holds : KParU7 := by
  intro X _ _ T hX Ls hL d Q hQ2 hd e
  exact exists_minOver_of_twistedA_even (m := 6) (by norm_num) (by decide) hX hL hQ2 hd e

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
