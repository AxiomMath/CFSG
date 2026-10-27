module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
public import Certificates.Data.O8p2NoDatum

public section

namespace CFSG.ClassicalInvolution.Q3.O8

open CFSG.EvenSmallLie.OmegaEight CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
  CFSG.ComponentClassification.J2Cover CFSG.ClassicalInvolution.O8Data

@[expose] def kGens (i : ℕ) : Array (Array ℕ) := ((centGens.getD i []).map omegaW).toArray

@[expose] def kS (i : ℕ) : Array (Array ℕ) := pushWords 360 (kGens i) (centDerived.getD i [])

@[expose] def kBaseF (i : ℕ) : List (Fin 360) := (centBase.getD i []).map fun b => Fin.ofNat 360 b

@[expose] def kBase (i : ℕ) : Array ℕ := ((kBaseF i).map Fin.val).toArray

@[expose] def kW (i : ℕ) : Array (List Int) := wordsOf 3 (centDerived.getD i [])

@[expose] def kChainCheck (i : ℕ) (sizes : List ℕ) : Bool :=
  rawChainOK 360 ((kS i).extract 0 3) (kS i) (kBase i) (kW i) 4 &&
    rawOrbitSizes 360 (kS i) (kBase i) == sizes

@[expose] def kCommCheck (i : ℕ) : Bool :=
  (centGens.getD i []).all (fun w => lettersOK 17 w) &&
    (List.range 3).all fun j => commArr (kS i)[j]! (mainArrs.getD i #[])

@[expose] def kWitList (i : ℕ) : List (Table × Table) :=
  (witWords.getD i []).map fun w =>
    (arrTable 360 (omegaW w), arrTable 360 (invCand 360 (omegaW w)))

@[expose] def kWitCheck (i : ℕ) : Bool :=
  (witWords.getD i []).all fun w => lettersOK 17 w &&
    isInvA 360 (omegaW w) (invCand 360 (omegaW w)) && commArr (omegaW w) (mainArrs.getD i #[])

@[expose] def witT (n : ℕ) (r : Table) (ws : List (Table × Table)) (c : Table) : Bool :=
  ws.any fun p =>
    let x := compT n c (compT n p.1 (compT n c p.2))
    tblEq n (compT n x x) (idT n) && !tblEq n x (idT n) && !tblEq n x r

@[expose] def sqTables (n : ℕ) (r : Table) (tabs : List (List Table)) : List Table :=
  filterProducts n (fun T => tblEq n (compT n T T) r) tabs (idT n) []

@[expose] def kSqCheck (i : ℕ) : Bool :=
  (sqTables 360 (arrTable 360 (mainArrs.getD i #[])) (chainTables 360 (kS i) (kBase i))).all
    (witT 360 (arrTable 360 (mainArrs.getD i #[])) (kWitList i))

@[expose] def closeGT : Array Table := (closeGens.map fun w => arrTable 360 (omegaW w)).toArray

@[expose] def closeGI : Array Table :=
  (closeGens.map fun w => arrTable 360 (invCand 360 (omegaW w))).toArray

@[expose] def closeGenCheck : Bool :=
  closeGens.all fun w => lettersOK 17 w && isInvA 360 (omegaW w) (invCand 360 (omegaW w))

@[expose] def classSizeCheck (i m : ℕ) : Bool :=
  let b := arrTable 360 (mainArrs.getD i #[])
  let c := conjClosureH 360 closeGT closeGI b m
  conjTreeOK 360 closeGT closeGI b c.1 c.2.1 c.2.2 && hkeysDistinct 360 c.1.toList &&
    decide (m ≤ c.1.size)

@[expose] def mainCheck (i : ℕ) : Bool :=
  siftA 360 (rawLevels 360 omegaS (omegaBase.map Fin.val).toArray)
    (omegaBase.map Fin.val).toArray 0 (mainArrs.getD i #[])

@[expose] def classCheck (i : ℕ) (sizes : List ℕ) (m : ℕ) : Bool :=
  kChainCheck i sizes && kCommCheck i && kWitCheck i && kSqCheck i && classSizeCheck i m &&
    mainCheck i

end CFSG.ClassicalInvolution.Q3.O8
