module

public import CFSG.GH74.AS16.E2.Pump2Tables
public import CFSG.GH74.AS16.E2.SzTables
public import CFSG.GH74.AS16.E2.OuterL33
public import CFSG.GH74.AS16.E2.OuterU33
public import CFSG.GH74.AS16.E2.Sz2
public import CFSG.GH74.E2.NoM12

public section

namespace CFSG.GH74.AS16.E2

open CFSG.GH74.E2 hiding Hyp
open CFSG.GH74.Uniqueness (S_CorZD)

theorem e2Leaves
    (hZD : S_CorZD) (hCL : ComponentList) (hD3 : K0Data3) : E2Leaves where
  a5nt := noPairA5NT_of hCL pumpUpData2 (CFSG.GH74.E2.NoM12.noComponent2M12_of hCL)
  l28 := noPairL28_of hD3 l28Data
  l33 := noPairL33_of_delta hZD hD3 smallData_L33 local3Data_L33
    (noPairL33Outer_of hZD hD3 smallData_L33)
  u33 := noPairU33_of hD3 smallData_U33 (noPairU33O_of hZD hD3 smallData_U33)
  sz8 := noPairSz8_of hD3 szData
  m11 := noPairM11_of_delta hZD hD3 smallData_M11 outTrivial_M11 local3Data_M11
  m12c := noPair2M12_of (CFSG.GH74.E2.NoM12.noComponent2M12_of hCL)
  sz8c := noPair2Sz8

end CFSG.GH74.AS16.E2
