module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalIndexU2
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalDiagU2
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalDiagU3

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

theorem unitaryRestSlice_holds : UnitaryRestSlice :=
  unitaryRestSlice_of_diag
    (fun h hℓ3 hq h3 y c hc hout ha hT => unitary_three_diag_false h hℓ3 hq h3 y c hc hout ha hT)
    (fun h hq hn y c hc => unitary_two_diag_false h hq hn y c hc)

end CFSG.HardMathSupport.Malle.E27Lie
