module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.Inputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.Line2B
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.Line4B
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.Line5A
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.Line5E
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.Line4A

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G] {a z : G}

theorem linesThrough_of_f5Local [Finite G] (hF : IsF5Type a z) (hL : F5Local G a z) :
    LinesThrough a z :=
  ⟨line_2B hF hL, line_4B hL, line_5A hL, line_5E hL, line_4A hF hL⟩

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
