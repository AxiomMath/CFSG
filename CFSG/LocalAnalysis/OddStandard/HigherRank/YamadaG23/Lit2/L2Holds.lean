module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Back
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2HoldsGriess
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2HoldsSpor
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitM22Out

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23


theorem l2Tables_holds : L2Tables :=
  ⟨l2Griess_holds, l2Sporadic_holds, CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput⟩

theorem gomi1RKP_of_literature
    (hP : GomiOuterPSLU4) (hLS : L2NoPauliPSL) (hUS : L2NoPauliPSU) (hOS : L2NoPauliPOmega) :
    Gomi1RKP :=
  gomi1RKP_of_inputs l2Tables_holds ⟨hP, gomiOuterM22_holds⟩ hLS hUS hOS

end CFSG.OddStandard.HigherRank.YamadaG23
