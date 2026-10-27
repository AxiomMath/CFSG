module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCGlue
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCNS1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCNS2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3

public section

namespace CFSG.OddStandard.SmallF3.FritzII

theorem fzc_caseI_of_sy3
    (h3 : FzCSy3) : FzCaseI :=
  fzc_of_split (fzc_sy_of fzc_sy1 fzc_sy2 h3) (fzc_ns_of fzc_ns1 fzc_ns2)

theorem fzc_caseI :
    FzCaseI :=
  fzc_caseI_of_sy3 fzc_sy3

end CFSG.OddStandard.SmallF3.FritzII
