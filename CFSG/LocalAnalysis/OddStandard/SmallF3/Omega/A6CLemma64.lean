module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CMainK
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6E8Main
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec64

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82Lemma64_of_certs
    (h33 : Asc82Lemma33) (h61 : Asc82Lemma61)
    (h63 : Asc82Lemma63) (hsh : Asc82Shapes) (hP : Asc82Tab6P) (hF : Asc82AutFacts)
    (hout : Asc82Outside) : Asc82Lemma64 :=
  asc82Lemma64_of h33 h63 hsh hP hF a6c_autCentChain3
    (asc82Case64E8_of h33 h61 h63 hsh hout a6c_autCentChain3 a6c_e8LayerFact a6c_autCentOmega5)
    hout

end CFSG.OddStandard.SmallF3.Omega
