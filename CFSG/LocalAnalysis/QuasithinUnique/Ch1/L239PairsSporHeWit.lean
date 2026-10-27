module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHe
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHeCnt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificate
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHe
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHeCnt
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificate
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHeWitInputs
public import Certificates.Certificate4090

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.HePairs

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.He
  CFSG.QuasithinUnique.K1.SporadicPerm

theorem he_wit_cert :
    CntOk 8330 ptAct heL2 heLabels2 r2a r2b q2s ∧
    Wit3Ok 8330 ptAct heL7 heLabels7 b7a q7a q7b ∧
    WitPOk 8330 ptAct heL7 heLabels7 7 b7p q7p :=
  Certificates.certificate4090

end CFSG.QuasithinUnique.Vol2Native.L239.HePairs
