module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GTri
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GBT
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Shared

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

section Certs

set_option linter.unusedSectionVars false


theorem t263FactGenK_of_residuals
    (hI : T263Families T263CaseIx) (hITD : T263CaseIxTD4)
    (hD : T263Families T263Desc) : T263FactGenK :=
  t263FactGenK_of_cases (fun p hp Y _ _ => lBalanceAt_holds Y p hp) t263Out_holds hI hITD
    (T263Families.of_apply fun _ => t263BT_holds _) hD

end Certs

end CFSG.LocalAnalysis.GLTheoremA.T263

end
