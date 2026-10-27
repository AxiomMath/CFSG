module

public import CFSG.LargeExtraspecial.AS35Eleven
public import CFSG.LargeExtraspecial.S12InspXMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

namespace S14

open CFSG.LargeExtraspecial.S4

theorem claim14_11_of'_core_narrow
    (h35 : AschbacherThreeTranspositionCore)
    (hTIs : CFSG.CGT.Timmesfeld75.SimpleCaseStmt) (hTI215 : CFSG.CGT.Timmesfeld75.Lemma215Stmt)
    (hARS : CFSG.Timmesfeld.ARSInput) (hTri : FischerTrialityInput)
    (hFischer : S12FischerStatement) (hInsp : Insp4FischerResidual)
    (h36 : Timmesfeld36Input) (hSL : S12SL4ModuleInput) (hNQ : NQIrredStmt)
    (hNQ6 : NQPlus6Stmt) (hD : DW.DempwolffLn2Input) (hCent : CentPlus6Stmt) :
    Claim14_11 :=
  claim14_11_of'_w4 (aschbacherSmithW4Input_of_core h35) hTIs hTI215 hARS hTri hFischer
    (insp4Input_of_fischerResidual hInsp) h36 hSL hNQ hNQ6 hD hCent

end S14

end CFSG.LargeExtraspecial
