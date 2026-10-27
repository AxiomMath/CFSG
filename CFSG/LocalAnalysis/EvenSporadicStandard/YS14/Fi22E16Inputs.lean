module

public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckInputs
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckInputs
public import CFSG.Monster.B.Fischer.Fi22OuterCheckInputs
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckInputs
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheckInputs
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.EvenSporadicStandard.YS14

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore

@[expose] def fi22E16Text : String :=
  include_str "../../../../Certificates/Data/CFSGNative/YS14/fi22-e16-3510.txt"

@[expose] def fi22E16Bytes : ByteArray := fi22E16Text.toUTF8

@[expose] def fi22E16Arr (L : Nat) : Array Nat := hexLine fi22E16Bytes 3 3510 L

@[expose] def fi22E16ProdA (k m : Nat) : Array Nat :=
  let f (i : Nat) : Array Nat := if m.testBit i then fi22E16Arr (4 * k + i) else idA 3510
  compA 3510 (compA 3510 (f 0) (f 1)) (compA 3510 (f 2) (f 3))

@[expose] def fi22E16Check (_ : Unit := ()) : Bool :=
  layoutOK fi22E16Bytes 3 3510 24 &&
  allLt 24 (fun L => isInvA 3510 (fi22E16Arr L) (invCand 3510 (fi22E16Arr L))) &&
  allLt 24 (fun L => fi22InP (fi22E16Arr L)) &&
  allLt 24 (fun L => eqA 3510 (compA 3510 (fi22E16Arr L) (fi22E16Arr L)) (idA 3510)) &&
  allLt 24 (fun L => eqA 3510 (compA 3510 (fi22E16Arr L) (fi22ExtArr (21 + L / 4)))
    (compA 3510 (fi22ExtArr (21 + L / 4)) (fi22E16Arr L))) &&
  allLt 24 (fun L => allLt 4 fun j =>
    eqA 3510 (compA 3510 (fi22E16Arr L) (fi22E16Arr (4 * (L / 4) + j)))
      (compA 3510 (fi22E16Arr (4 * (L / 4) + j)) (fi22E16Arr L))) &&
  allLt 6 (fun k => allLt 16 fun m => allLt 16 fun m' =>
    m == m' || !(eqA 3510 (fi22E16ProdA k m) (fi22E16ProdA k m')))

end CFSG.EvenSporadicStandard.YS14
