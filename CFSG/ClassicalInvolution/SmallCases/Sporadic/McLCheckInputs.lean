module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.McLData
public import Certificates.Data.CFSGNative.Co3Schreier.Orbit

public section

namespace CFSG.ClassicalInvolution
namespace McLProof

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native
  CFSG.ClassicalInvolution.McLData

@[expose] def capK : Nat := 50000

@[expose] def lbOK (n cap m : Nat) (gs : List Table) : Bool :=
  let A := gs.toArray
  let E := mulClosureH n A cap
  mulTreeOK n A E.1 E.2.1 E.2.2 && hkeysDistinct n E.1.toList && E.1.size == m

@[expose] def abArr : Array (Array Nat) := #[natArr Ta, natArr Tb]

@[expose] def zArr : Array Nat := abArr[0]!

@[expose] def fixZ : List Nat := fixedList 275 zArr

@[expose] def orbZ : Array (List Nat) × Array Nat × Array Nat := hashSearch abArr fixZ 22275

@[expose] def repClosures : List (Table × (Array Table × Array Nat × Array Nat)) :=
  repTbls.map fun r => (r, conjClosureH 275 kgens.toArray (kgens.toArray.map (invT 275)) r capK)

@[expose] def coverOK : Bool :=
  repClosures.all (fun c => conjTreeOK 275 kgens.toArray (kgens.toArray.map (invT 275)) c.1
    c.2.1 c.2.2.1 c.2.2.2) &&
    hkeysDistinct 275 ([idT 275, Ta] ++ repClosures.flatMap fun c => c.2.1.toList) &&
    (repClosures.map fun c => c.2.1.size).sum + 2 == 40320

@[expose] def kx : Table := kgens[0]!

@[expose] def ky : Table := kgens[1]!

@[expose] def commOK : Bool :=
  let c := compT 275 (compT 275 kx ky) (compT 275 (invT 275 kx) (invT 275 ky))
  !tblEq 275 c (idT 275) && !tblEq 275 c Ta

@[expose] def sylowCoverOK : Bool :=
  (mulClosureH 275 sgens.toArray capK).1.all fun T =>
    !(involOK 275 T) || conjTbls.any (tblEq 275 T)

end McLProof
end CFSG.ClassicalInvolution
