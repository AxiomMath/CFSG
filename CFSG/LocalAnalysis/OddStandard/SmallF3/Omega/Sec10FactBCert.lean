module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10PkI4

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82FactB5_of_cert :
    Asc82FactB5 :=
  asc82FactB5_of_pockets (fun hc h => isI4PlusIn_of_conj_tA hc h)
    (fun hc h => not_isI4PlusIn_of_conj_tB hc h)

end CFSG.OddStandard.SmallF3.Omega
