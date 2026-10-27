module

public import CFSG.GH74.Generic.Front.NoCentral
public import CFSG.GH74.Generic.Front.Props

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank

theorem noCentralStatement : NoCentralStatement := by
  intro K _ hK
  rcases hK with (⟨F, _, _, hF, ⟨e⟩⟩ | ⟨q, F, _, _, hF, hq, ⟨e⟩⟩) | ⟨F, _, _, hodd, ⟨e⟩⟩
  · exact NoCentral.of_mulEquiv e (noCentral_statedSL4 hF)
  · exact NoCentral.of_mulEquiv e (noCentral_statedSU4 hF hq)
  · exact NoCentral.of_mulEquiv e (noCentral_statedSp2 hodd)

end CFSG.GH74.Generic
