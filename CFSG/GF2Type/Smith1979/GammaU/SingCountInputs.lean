module

public import CFSG.GF2Type.Smith1979.GammaU.Bits

public section

namespace CFSG.GF2Type.Smith1979.GammaU

@[expose] def singCodes (_ : Unit := ()) : List ℕ :=
  (List.range 4096).filter fun n => n != 0 && !q0b n

@[expose] def singCount (_ : Unit := ()) : Bool := (singCodes ()).length == 2079

end CFSG.GF2Type.Smith1979.GammaU
