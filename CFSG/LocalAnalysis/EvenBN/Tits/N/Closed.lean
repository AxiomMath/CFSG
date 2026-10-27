module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Current
public import CFSG.LocalAnalysis.EvenBN.Tits.N.KappaD
public import CFSG.LocalAnalysis.EvenBN.Tits.N.KappaAhatMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N


theorem titsThm49StatementExclusion_holds :
    CFSG.Yardstones.M41b0c98b3153.TitsThm49StatementExclusion :=
  titsThm49StatementExclusion_of_open (stepKappaBit_of_split stepKappaBitD_holds stepKappaBitAhat_holds)

end CFSG.LocalAnalysis.EvenBN.Tits.N
