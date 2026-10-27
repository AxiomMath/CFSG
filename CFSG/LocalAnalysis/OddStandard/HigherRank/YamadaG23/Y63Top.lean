module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Final
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63Cert
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LHS

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open CFSG.OddStandard.HigherRank.G2Three CFSG.OddStandard.HigherRank.G2Three.Sec2

theorem sec63'_of_cert
    (hB : Sec3Inputs) (h26HS : Lemma26HS) (hfin : Finite TauCeti.SporadicName.HS.Group) :
    Sec63' :=
  sec63'_of hB (hsSylowFacts_of_cert h26HS hfin)

theorem sec63'_of_certs
    (hB : Sec3Inputs) :
    Sec63' :=
  sec63'_of_cert hB lemma26HS_holds CFSG.Sporadic.Presentation.HS.finite_card_le.1

end CFSG.OddStandard.HigherRank.YamadaG23
