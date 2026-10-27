module

public import CFSG.HardMathSupport.Dickson.BMRows.CensusM3
public import CFSG.HardMathSupport.Dickson.BMRows.CensusM5
public import CFSG.HardMathSupport.Dickson.BMRows.CensusM7
import CFSG.HardMathSupport.Dickson.BMRows.RowsM
import CFSG.HardMathSupport.Dickson.BMRows.Types
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporRows

public section

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.HardMathSupport.Dickson.I271 (M3ResBNoComp CentFiveBNoComp)
open CFSG.HardMathSupport.Solomon.Coordinator (sporadicOrdersTable_holds lieOrderBridge_holds)

section Rows

section M3KGroup

theorem arow_M_three_of_kGroup (hK : CFSG.Open.IsKGroup (Carrier .M)) : I1415Rows.I1415Row .M 3 :=
  arow_M_of_census (census_M_three hK) (atypeOK_M3 sporadicOrdersTable_holds)

theorem srow_M_three_of_kGroup (hK : CFSG.Open.IsKGroup (Carrier .M)) : SporAltRows.SRow .M 3 :=
  srow_M_of_census (census_M_three hK) (stypeOK_M3 sporadicOrdersTable_holds)

theorem kdSporRow_M_three_of_kGroup (hK : CFSG.Open.IsKGroup (Carrier .M)) : KDSporRow .M 3 :=
  kdSporRow_M_of_census (by norm_num) (by norm_num) (census_M_three hK) kLevel_M3

theorem kdl227Row_M_of_kGroup (hK : CFSG.Open.IsKGroup (Carrier .M)) :
    KDL227Rows.KDL227SporRow .M :=
  kdl227Row_M_of_census (census_M_three hK) (notL227_M3 sporadicOrdersTable_holds)

theorem row_M_three_of_kGroup (hK : CFSG.Open.IsKGroup (Carrier .M)) :
    I1416Rows.I1416SporRow .M 3 :=
  row_M_of_census (census_M_three hK) (typeOK_M3 sporadicOrdersTable_holds lieOrderBridge_holds)

theorem qrow_M_three_of_kGroup (hK : CFSG.Open.IsKGroup (Carrier .M)) : I1416QRows.I1416QRow .M 3 :=
  qrow_M_of_census (census_M_three hK) (qtypeOK_M3 sporadicOrdersTable_holds lieOrderBridge_holds)

end M3KGroup

section M5KGroup

theorem arow_M_five_of_kGroup
    (hK : CFSG.Open.IsKGroup (Carrier .M)) : I1415Rows.I1415Row .M 5 :=
  arow_M_of_census (census_M_five hK) (atypeOK_M5 sporadicOrdersTable_holds)

theorem kdSporRow_M_five_of_kGroup
    (hK : CFSG.Open.IsKGroup (Carrier .M)) : KDSporRow .M 5 :=
  kdSporRow_M_of_census (by norm_num) (by norm_num) (census_M_five hK) kLevel_M5

theorem row_M_five_of_kGroup
    (hK : CFSG.Open.IsKGroup (Carrier .M)) : I1416Rows.I1416SporRow .M 5 :=
  row_M_of_census (census_M_five hK) (typeOK_M5 sporadicOrdersTable_holds lieOrderBridge_holds)

theorem qrow_M_five_of_kGroup
    (hK : CFSG.Open.IsKGroup (Carrier .M)) : I1416QRows.I1416QRow .M 5 :=
  qrow_M_of_census (census_M_five hK) (qtypeOK_M5 sporadicOrdersTable_holds lieOrderBridge_holds)

end M5KGroup

section M7

theorem arow_M_seven
    : I1415Rows.I1415Row .M 7 :=
  arow_M_of_census census_M_seven (atypeOK_M7 sporadicOrdersTable_holds)

theorem kdSporRow_M_seven
    : KDSporRow .M 7 :=
  kdSporRow_M_of_census (by norm_num) (by norm_num) census_M_seven kLevel_M7

section Lie

theorem row_M_seven
    : I1416Rows.I1416SporRow .M 7 :=
  row_M_of_census census_M_seven (typeOK_M7 sporadicOrdersTable_holds lieOrderBridge_holds)

theorem qrow_M_seven
    : I1416QRows.I1416QRow .M 7 :=
  qrow_M_of_census census_M_seven (qtypeOK_M7 sporadicOrdersTable_holds lieOrderBridge_holds)

end Lie

end M7

end Rows

end CFSG.HardMathSupport.Dickson.BMRows
