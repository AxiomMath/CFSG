module

public import CFSG.HardMathSupport.Dickson.BMRows.CensusB3
public import CFSG.HardMathSupport.Dickson.BMRows.CensusB5
public import CFSG.HardMathSupport.Dickson.BMRows.CensusB7
public import CFSG.HardMathSupport.Dickson.BMRows.Rows
public import CFSG.HardMathSupport.Dickson.BMRows.TypesSeven
import CFSG.HardMathSupport.Dickson.BMRows.RowsB
import CFSG.HardMathSupport.Dickson.BMRows.Types

public section

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.HardMathSupport.Dickson.I271 (TabBThreeBNoComp TabBFiveBNoComp)
open CFSG.HardMathSupport.Solomon.Coordinator (sporadicOrdersTable_holds lieOrderBridge_holds)

section Rows

section B3KGroup

theorem arow_B_three_of_kGroup
    (hK : CFSG.Open.IsKGroup (Carrier .B)) : I1415Rows.I1415Row .B 3 :=
  arow_B_of_census (census_B_three hK) (atypeOK_B3 sporadicOrdersTable_holds)

theorem srow_B_three_of_kGroup
    (hK : CFSG.Open.IsKGroup (Carrier .B)) : SporAltRows.SRow .B 3 :=
  srow_B_of_census (census_B_three hK) (stypeOK_B3 sporadicOrdersTable_holds)

theorem kdSporRow_B_three_of_kGroup
    (hK : CFSG.Open.IsKGroup (Carrier .B)) : KDSporRow .B 3 :=
  kdSporRow_B_of_census (by norm_num) (by norm_num) (census_B_three hK) kLevel_B3

theorem kdl227Row_B_of_kGroup
    (hK : CFSG.Open.IsKGroup (Carrier .B)) :
    KDL227Rows.KDL227SporRow .B :=
  kdl227Row_B_of_census (census_B_three hK) (notL227_B3 sporadicOrdersTable_holds)

theorem row_B_three_of_kGroup
    (hK : CFSG.Open.IsKGroup (Carrier .B)) :
    I1416Rows.I1416SporRow .B 3 :=
  row_B_of_census (census_B_three hK) (typeOK_B3 sporadicOrdersTable_holds lieOrderBridge_holds)

theorem qrow_B_three_of_kGroup
    (hK : CFSG.Open.IsKGroup (Carrier .B)) : I1416QRows.I1416QRow .B 3 :=
  qrow_B_of_census (census_B_three hK) (qtypeOK_B3 sporadicOrdersTable_holds lieOrderBridge_holds)

end B3KGroup

section B5KGroup

theorem arow_B_five_of_kGroup
    (hK : CFSG.Open.IsKGroup (Carrier .B)) : I1415Rows.I1415Row .B 5 :=
  arow_B_of_census (census_B_five hK) (atypeOK_B5 sporadicOrdersTable_holds)

theorem kdSporRow_B_five_of_kGroup
    (hK : CFSG.Open.IsKGroup (Carrier .B)) : KDSporRow .B 5 :=
  kdSporRow_B_of_census (by norm_num) (by norm_num) (census_B_five hK) kLevel_B5

theorem row_B_five_of_kGroup
    (hK : CFSG.Open.IsKGroup (Carrier .B)) : I1416Rows.I1416SporRow .B 5 :=
  row_B_of_census (census_B_five hK) (typeOK_B5 sporadicOrdersTable_holds lieOrderBridge_holds)

theorem qrow_B_five_of_kGroup
    (hK : CFSG.Open.IsKGroup (Carrier .B)) : I1416QRows.I1416QRow .B 5 :=
  qrow_B_of_census (census_B_five hK) (qtypeOK_B5 sporadicOrdersTable_holds lieOrderBridge_holds)

end B5KGroup

section B7

theorem arow_B_seven
    : I1415Rows.I1415Row .B 7 :=
  arow_B_of_cardCensus (census_B_seven : PCardCensus 7 (Carrier .B) 80640) atypeOK_B7

section Lie

theorem row_B_seven
    : I1416Rows.I1416SporRow .B 7 :=
  row_B_of_cardCensus (census_B_seven : PCardCensus 7 (Carrier .B) 80640)
    (typeOK_B7 lieOrderBridge_holds)

theorem qrow_B_seven
    : I1416QRows.I1416QRow .B 7 :=
  qrow_B_of_cardCensus (census_B_seven : PCardCensus 7 (Carrier .B) 80640)
    (qtypeOK_B7 lieOrderBridge_holds)

end Lie

end B7

end Rows

end CFSG.HardMathSupport.Dickson.BMRows
