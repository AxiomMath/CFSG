module

public import CFSG.Sporadic.SmallOddCore.J3CheckInputs

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Schreier.Native CFSG.Certificates.Native

set_option compiler.extract_closed false

@[expose] def j3OuterWitTbl (_ : Unit := ()) : Table :=
  let t := j3CentTbl 21
  let b := j3PGTbls[1]!
  compT 6156 t (compT 6156 b (compT 6156 t (compT 6156 b b)))

@[expose] def j3OuterWitCheck (_ : Unit := ()) : Bool :=
  let y := j3OuterWitTbl ()
  permOK 6156 (j3CentTbl 21) && tblEq 6156 (powT 6156 19 y) (idT 6156) &&
    !tblEq 6156 y (idT 6156)

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
