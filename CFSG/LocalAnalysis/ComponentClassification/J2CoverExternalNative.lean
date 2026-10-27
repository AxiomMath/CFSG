
module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalData
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsNative
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckInputs
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

public section

namespace CFSG.ComponentClassification.J2Cover.External

open CFSG.Sporadic.Th.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.J2Cover (inP commA arrTable chainTables invoList movesList
  fixedCount)
open CFSG.ComponentClassification.J2Cover.Models (bArr repArrs eltArrs fRows aCoefT invTab betaTab
  mulTab bitAt lamBit xorFold)

@[expose] def inC (t : Array Nat) : Bool :=
  siftA 315 (rawLevels 315 fixCStrong fixCBase) fixCBase 0 t

@[expose] def inD (t : Array Nat) : Bool :=
  siftA 315 (rawLevels 315 fixDStrong fixDBase) fixDBase 0 t

@[expose] def tblX : Table := arrTable 315 fixDStrong[0]!

@[expose] def tblY : Table := arrTable 315 fixDStrong[1]!

@[expose] def dOrderTables (m : Nat) : List Table :=
  filterProducts 315 (ordTest 315 m) (chainTables 315 fixDStrong fixDBase) (idT 315) []

@[expose] def tblFix (T : Table) : Nat := (List.range 315).countP fun i => ap T i == i

@[expose] def commArr (a b : Array Nat) : Array Nat :=
  compA 315 a (compA 315 b (compA 315 (invCand 315 a) (invCand 315 b)))

@[expose] def chainCheck : Bool :=
  rawChainOK 315 (fixCStrong.extract 0 2) fixCStrong fixCBase fixCWords 4 &&
  rawOrbitSizes 315 fixCStrong fixCBase == [21, 16] &&
  inP fixCStrong[0]! && inP fixCStrong[1]! &&
  commA fixCStrong[0]! bArr && commA fixCStrong[1]! bArr &&
  rawChainOK 315 (fixDStrong.extract 0 2) fixDStrong fixDBase fixDWords 4 &&
  rawOrbitSizes 315 fixDStrong fixDBase == [168] &&
  inC fixDStrong[0]! && inC fixDStrong[1]! &&
  rawChainOK 315 (fixWStrong.extract 0 2) fixWStrong fixWBase fixWWords 4 &&
  rawOrbitSizes 315 fixWStrong fixWBase == [8] &&
  inD fixWStrong[0]! && inD fixWStrong[1]!

@[expose] def tableCheck : Bool :=
  ordTest 315 2 tblX && ordTest 315 3 tblY && pairTest 315 7 4 2 3 tblX tblY &&
  (dOrderTables 2).length == 21 && (dOrderTables 2).all (fun T => tblFix T == 11) &&
  pairCount (dOrderTables 2) (dOrderTables 3) (fun x y => ordW 315 [x, y] 7) == 336 &&
  pairCount (dOrderTables 2) (dOrderTables 3) (pairTest 315 7 4 2 3) == 336 &&
  countProducts 315 (commAll 315 [tblX, tblY]) (chainTables 315 fixCStrong fixCBase)
    (idT 315) == 1

@[expose] def elemCheck : Bool :=
  ordTest 315 4 (arrTable 315 fixWStrong[0]!) && ordTest 315 2 (arrTable 315 fixWStrong[1]!) &&
  isInvA 315 fixWStrong[0]! (invCand 315 fixWStrong[0]!) &&
  eqA 315 (compA 315 fixWStrong[1]! (compA 315 fixWStrong[0]! fixWStrong[1]!))
    (invCand 315 fixWStrong[0]!) &&
  !(eqA 315 fixWStrong[1]! (compA 315 fixWStrong[0]! fixWStrong[0]!)) &&
  invoList 315 fusionArr && movesList 315 fusionArr && fixedCount 315 fusionArr == 15 &&
  inC fusionArr && !(inD fusionArr) &&
  allLt 4 (fun k => isInvA 315 commArrs[k]! (invCand 315 commArrs[k]!) && inD commArrs[k]!) &&
  eqA 315 fixDStrong[0]! (commArr commArrs[0]! commArrs[1]!) &&
  eqA 315 fixDStrong[1]! (commArr commArrs[2]! commArrs[3]!)

@[expose] def fusionBit (i : Nat) : Bool :=
  let s := aCoefT[i]!
  let si := invTab[s]!
  let p := fusionP[i]!
  let bp := betaTab[p]!
  bitAt fRows si s ^^ lamBit p ^^ bitAt fRows si bp ^^
    bitAt fRows mulTab[si]![bp]! aCoefT[fusionI[i]!]!

@[expose] def lamCheck : Bool :=
  allLt 4725 (fun i => decide (fusionP[i]! < 128) && decide (fusionI[i]! < 4725) &&
    eqA 315 (compA 315 repArrs[i]! fusionArr)
      (compA 315 eltArrs[fusionP[i]!]! repArrs[fusionI[i]!]!)) &&
  xorFold 4725 fusionBit

end CFSG.ComponentClassification.J2Cover.External
