module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434Cases
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434AltCase
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434SporHeavy
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434DefCase
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434Exc
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClMain
public import CFSG.RankThree.PartOne.TCB.Final

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor


theorem kFactI1434_holds : KFactI1434 :=
  kFactI1434_of_cases RankThree.PartOne.TCB.tauCetiCatalogBridge i1434AltCase_holds
      i1434SporCase_holds i1434DefCase_holds I1434Exc.i1434ExcCase_holds i1434ClassicalCase_holds

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
