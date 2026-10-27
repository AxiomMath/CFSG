module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeModelsData
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaData
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeAutSylowTests

public section

namespace CFSG.ComponentClassification.AS81.HeTri

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer
open CFSG.ComponentClassification.AS81.HeSylow CFSG.ComponentClassification.AS81.Hexa

@[expose] def certK (n : ℕ) (ps : List ℕ) (gs : List (Array ℕ)) (m : ℕ) : ArrCert :=
  enumBfs n gs.toArray ps (m + 1)

@[expose] def eltsK (n : ℕ) (ps : List ℕ) (gs : List (Array ℕ)) (m : ℕ) : List (Array ℕ) :=
  (certK n ps gs m).pts.toList

@[expose] def enumCheckK (n : ℕ) (ps : List ℕ) (gs : List (Array ℕ)) (m : ℕ) : Bool :=
  enumOK n gs.toArray ps (certK n ps gs m) && (certK n ps gs m).pts.size == m

@[expose] def base64 : List ℕ := [0, 1, 2, 4, 8, 16, 32]

@[expose] def base32 : List ℕ := [1, 2, 4, 8, 16]

@[expose] def heP12Gens : List (Array ℕ) := hexaTGens ++ hexaCGens

@[expose] def heTL : List (Array ℕ) := eltsK 64 base64 hexaTGens 64
@[expose] def heML : List (Array ℕ) := eltsK 64 base64 hexaMGens 2160
@[expose] def heP12L : List (Array ℕ) := eltsK 64 base64 heP12Gens 3072
@[expose] def heBL : List (Array ℕ) := eltsK 64 base64 heB0Gens 1024
@[expose] def heFL : List (Array ℕ) := eltsK 64 base64 heF0Gens 64
@[expose] def heCL : List (Array ℕ) := eltsK 32 base32 hePCGens 21504
@[expose] def heBCL : List (Array ℕ) := eltsK 32 base32 heBCGens 1024
@[expose] def heP0L : List (Array ℕ) := eltsK 32 base32 heP12CGens 3072
@[expose] def heP1L : List (Array ℕ) := eltsK 32 base32 heP13CGens 3072
@[expose] def heU0L : List (Array ℕ) := eltsK 32 base32 heECGens 64
@[expose] def heU1L : List (Array ℕ) := eltsK 32 base32 heFCGens 64

@[expose] def normsN (n : ℕ) (F fs : List (Array ℕ)) (x : Array ℕ) : Bool :=
  fs.all fun f => inLN n F (conjA n x f)

@[expose] def stabW (k : ℕ) (x : Array ℕ) : Bool :=
  (List.range (2 ^ k)).all fun v => decide (x[v]! < 2 ^ k)

@[expose] def unipW (k : ℕ) (x : Array ℕ) : Bool :=
  (List.range (2 ^ k)).all (fun v => x[v]! == v) &&
    (List.range 32).all fun v => decide (Nat.xor x[v]! v < 2 ^ k)

@[expose] def inTMN (g : Array ℕ) : Bool :=
  heTL.any fun t => inLN 64 heML (compA 64 (invCand 64 t) g)

@[expose] def heCheckEnum : Bool :=
  enumCheckK 64 base64 hexaTGens 64 && enumCheckK 64 base64 hexaMGens 2160 &&
    enumCheckK 64 base64 heP12Gens 3072 && enumCheckK 64 base64 heB0Gens 1024 &&
    enumCheckK 64 base64 heF0Gens 64 && enumCheckK 64 base64 heP23Gens 9216 &&
    enumCheckK 32 base32 hePCGens 21504 && enumCheckK 32 base32 heBCGens 1024 &&
    enumCheckK 32 base32 heP12CGens 3072 && enumCheckK 32 base32 heP13CGens 3072 &&
    enumCheckK 32 base32 heECGens 64 && enumCheckK 32 base32 heFCGens 64 &&
    validA 64 heZetaArr && validA 64 hexaT0 && validA 32 heTCArr

@[expose] def heCheckZeta : Bool :=
  heTL.all (fun t => !(inLN 64 heML t) || eqA 64 t (idA 64)) &&
    inLN 64 heML heZetaArr && eqA 64 (powN 64 heZetaArr 3) (idA 64) &&
    !(eqA 64 heZetaArr (idA 64)) &&
    heTL.all (fun t => !(commN 64 heZetaArr t) || eqA 64 t (idA 64)) &&
    heML.all fun m => eqA 64 (conjA 64 m heZetaArr) heZetaArr ||
      eqA 64 (conjA 64 m heZetaArr) (powN 64 heZetaArr 2)

@[expose] def heCheckOrbit : Bool :=
  heTL.all fun t => eqA 64 t (idA 64) || heML.any (fun m => eqA 64 (conjA 64 m t) hexaT0) ||
    heML.any fun m => commN 64 m t && eqA 64 (powN 64 m 5) (idA 64) && !(eqA 64 m (idA 64))

@[expose] def heCheckB0 : Bool :=
  hexaTGens.all (fun a => hexaTGens.all (commN 64 a)) && inLN 64 heTL hexaT0 &&
    hexaCGens.all (inLN 64 heML) && hexaCGens.all (fun g => commN 64 g hexaT0) &&
    heB0Gens.all (inLN 64 heP12L) && hexaTGens.all (inLN 64 heBL) &&
    heF0Gens.all (inLN 64 heBL) && heFL.all (fun x => eqA 64 (mulN 64 x x) (idA 64)) &&
    heFL.any (fun x => !(inLN 64 heTL x)) && heB0Gens.all (normsN 64 heFL heF0Gens) &&
    uniqEN 64 heBL heTL heFL

@[expose] def heCheckP23 : Bool :=
  heP23Gens.all inTMN && heP23Gens.all (normsN 64 heFL heF0Gens) &&
    heP23Gens.all (fun g => eqA 64 (powN 64 g 8) (idA 64)) &&
    (heML.filter (normsN 64 heFL heF0Gens)).length == 144

@[expose] def heCheckC : Bool :=
  inLN 32 heCL heTCArr &&
    heCL.all (fun x => !(hePCGens.all (commN 32 x)) || eqA 32 x (idA 32) || eqA 32 x heTCArr) &&
    heBCGens.all (inLN 32 heP0L) && heBCGens.all (inLN 32 heP1L) &&
    heP12CGens.all (inLN 32 heCL) && heP13CGens.all (inLN 32 heCL) &&
    heECGens.all (inLN 32 heP0L) && heFCGens.all (inLN 32 heP1L) &&
    heECGens.all (inLN 32 heBCL) && heFCGens.all (inLN 32 heBCL) &&
    heU0L.all (fun x => eqA 32 (mulN 32 x x) (idA 32)) &&
    heU1L.all (fun x => eqA 32 (mulN 32 x x) (idA 32)) &&
    inLN 32 heU0L heTCArr && inLN 32 heU1L heTCArr &&
    uniqEN 32 heBCL heU0L heU1L &&
    heP12CGens.any (fun g => heFCGens.any fun f => !(inLN 32 heU1L (conjA 32 g f))) &&
    heP13CGens.any (fun g => heECGens.any fun f => !(inLN 32 heU0L (conjA 32 g f))) &&
    heCL.all (fun x => !(heECGens.all (commN 32 x)) || inLN 32 heU0L x) &&
    heCL.all (fun x => !(heFCGens.all (commN 32 x)) || inLN 32 heU1L x) &&
    heP12CGens.all (normsN 32 heU0L heECGens) && heP13CGens.all (normsN 32 heU1L heFCGens)

@[expose] def heCheckCount : Bool :=
  (heCL.filter (stabW 2)).length == 3072 && (heCL.filter (stabW 3)).length == 3072 &&
    heP0L.all (stabW 2) && heP1L.all (stabW 3) && (heP0L.filter (stabW 3)).length == 1024 &&
    (heCL.filter (unipW 2)).length == 64 && (heCL.filter (unipW 3)).length == 64 &&
    heU0L.all (unipW 2) && heU1L.all (unipW 3) &&
    (heCL.filter fun x => heECGens.all fun f => unipW 2 (conjA 32 x f)).length == 3072 &&
    (heCL.filter fun x => heFCGens.all fun f => unipW 3 (conjA 32 x f)).length == 3072

@[expose] def heModelCheck : Bool :=
  heCheckEnum && heCheckZeta && heCheckOrbit && heCheckB0 && heCheckP23 && heCheckC &&
    heCheckCount

end CFSG.ComponentClassification.AS81.HeTri
