module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127FFK
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Final

public section

namespace CFSG.Quasithin

theorem c127FFKInput_of (h113 : CFSG.ASVolI.B_1_13) (hblock : C127KBlockType) : C127FFKInput :=
  ⟨h113, hblock, CFSG.QuasithinUnique.L246C127.altEvenExcludedBig⟩

theorem theoremC127_of_b113_blockType
    (h113 : CFSG.ASVolI.B_1_13) (hblock : C127KBlockType) : TheoremC127 :=
  theoremC127_of_ffK (c127FFKInput_of h113 hblock)

end CFSG.Quasithin
