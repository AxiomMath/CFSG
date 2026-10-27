module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRuDcInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCore

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat.RuCert

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
open CFSG.Sporadic.Ru.Native (ruData)

@[expose] noncomputable def ruSgK : List (J ruData) :=
  ruQp.map fun p => (slpElts (a ruData) (b ruData) ruProg).getD p.1 1

end CFSG.QuasithinUnique.Ch1.SporLat.RuCert

end
