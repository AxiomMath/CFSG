module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf4Sp0Fin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf2Om0Gen

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

set_option linter.unusedSectionVars false

namespace Twin1711

structure PfTablesRest : Prop where
  sp1 : NoSandwichAt ModSp1
  om1 : NoSandwichAt ModOm1
  om2 : SandwichSizeTwoAt ModOm2
  om2p : PairingAt ModOm2

section Assemble


theorem pfTables_of_rest (hR : PfTablesRest) : PfTables :=
  { sp0 := Twin1711.Sp0K.sp0_proved
    sp1 := hR.sp1
    om0 := Twin1711.Om0.om0_proved
    om1 := hR.om1
    om2 := hR.om2
    om2p := hR.om2p }

end Assemble

end Twin1711

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

