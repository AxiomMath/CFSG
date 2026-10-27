module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
public import Certificates.Data.CFSGNative.SporadicSchreier.Count

@[expose] public section

namespace CFSG.ComponentClassification.J2Cover

open CFSG.Sporadic.Th.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.Native

@[expose] def tblA : Table := arrTable 315 autStrong[0]!

@[expose] def tblB : Table := arrTable 315 autStrong[1]!

@[expose] def tblAInv : Table := arrTable 315 (invCand 315 autStrong[0]!)

@[expose] def tblBInv : Table := arrTable 315 (invCand 315 autStrong[1]!)

@[expose] def tblU : Table := arrTable 315 outerArr

@[expose] def tblTwoA : Table := arrTable 315 twoAArr

@[expose] def autLevels : Array Level := rawLevels 315 autStrong autBase

@[expose] def autTables : List (List Table) := chainTables 315 autStrong autBase

@[expose] def orderTablesOf (g : Table) (m : Nat) : List Table :=
  filterProducts 315 (ordTest 315 m) autTables g []

@[expose] def inP (t : Array Nat) : Bool := siftA 315 autLevels autBase 0 t

@[expose] def commA (t r : Array Nat) : Bool := eqA 315 (compA 315 t r) (compA 315 r t)

end CFSG.ComponentClassification.J2Cover
