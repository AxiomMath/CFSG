module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2ThreeKit
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporCo2E81Data
public import CFSG.Monster.B.Mathieu.SylowCore
public import Certificates.Data.CFSGNative.Co3Schreier.Basic
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2ThreeKit
public meta import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporCo2E81Data
public meta import CFSG.Monster.B.Mathieu.SylowCore
public meta import Certificates.Data.CFSGNative.Co3Schreier.Basic
public meta import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeKit
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeKit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public meta import CFSG.LocalAnalysis.GLTheoremB.QuotientTools

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert
  CFSG.RankThree.PartTwo.Sec4.Item434SporE81 CFSG.Sporadic.Schreier.Co3.Native

@[expose] def hypTuples : Array (Array Nat) :=
  #[#[2, 769, 1599, 1130, 1842, 1396], #[3, 2163, 1785, 1920, 2013, 1710],
    #[3, 2045, 1013, 1542, 302, 1092], #[2, 2254, 1534, 733, 518, 1007],
    #[8, 1044, 920, 1987, 569, 952], #[8, 1044, 2011, 1234, 785, 952],
    #[3, 2163, 1785, 1222, 2013, 1710], #[2, 595, 188, 1246, 1540, 486],
    #[8, 788, 1743, 1809, 977, 2156], #[2, 23, 1375, 166, 961, 623],
    #[9, 1925, 1724, 445, 1249, 460], #[2, 595, 540, 135, 49, 1687], #[2, 23, 177, 656, 961, 478],
    #[8, 752, 920, 1753, 1613, 1003], #[2, 2254, 540, 733, 1002, 148],
    #[2, 23, 1868, 1697, 518, 1853], #[3, 1518, 1233, 1519, 308, 186],
    #[3, 618, 86, 1222, 1435, 1129], #[2, 23, 1868, 432, 518, 1853],
    #[3, 245, 900, 1954, 498, 1652], #[2, 595, 564, 166, 49, 1804],
    #[3, 2163, 431, 2021, 1591, 1052], #[2, 2269, 949, 1697, 1002, 148],
    #[2, 23, 1375, 2068, 961, 623], #[8, 752, 1193, 1961, 1466, 1463],
    #[3, 245, 1405, 151, 1591, 1052], #[2, 23, 1534, 656, 518, 1376],
    #[3, 245, 1405, 1384, 1591, 1052], #[2, 595, 188, 432, 1540, 2014],
    #[3, 2163, 1518, 87, 2013, 1310], #[3, 2045, 1459, 2224, 584, 1659],
    #[3, 2163, 1518, 1921, 2013, 1310], #[2, 769, 1375, 2068, 1540, 486],
    #[3, 245, 1785, 161, 498, 1619], #[3, 2163, 1459, 1519, 2013, 928],
    #[8, 154, 1503, 444, 1393, 73], #[8, 752, 1044, 977, 1621, 1283],
    #[8, 752, 2083, 1210, 2194, 107], #[8, 154, 1503, 1961, 1466, 1463],
    #[3, 618, 1459, 2021, 584, 1349]]

@[expose] def hypFuncs : Array Nat :=
  #[27, 9, 36, 63, 3, 30, 57, 12, 39, 66, 21, 48, 75, 1, 28, 55, 10, 37, 64, 19, 46, 73, 4, 31,
    58, 13, 40, 67, 22, 49, 76, 7, 34, 61, 16, 43, 70, 25, 52, 79]

@[expose] def relPairs : Array (Nat × Nat) := #[(0, 1), (0, 2), (0, 3), (4, 5)]

@[expose] def levels (_ : Unit := ()) : Array Level := rawLevels 2300 co2StrongArrs co2BaseArr

@[expose] def inP (L : Array Level) (g : Array Nat) : Bool := siftA 2300 L co2BaseArr 0 g

@[expose] def qGens2 (_ : Unit := ()) : Array (Array Nat) := qGens co2E81

@[expose] def qCert2 (_ : Unit := ()) : ArrCert := qCert co2E81

@[expose] def dGens (_ : Unit := ()) : Array (Array Nat) :=
  (co2E81.dW[0]!).map (posWord 2300 (qGens2 ()))

@[expose] def hGens (_ : Unit := ()) : Array (Array Nat) := hArrs co2E81

@[expose] def digit3 (k i : Nat) : Nat := k / 3 ^ i % 3

@[expose] def dProd (dg : Array (Array Nat)) (k : Nat) : Array Nat :=
  compA 2300 (powArr 2300 dg[0]! (digit3 k 0)) (compA 2300 (powArr 2300 dg[1]! (digit3 k 1))
    (compA 2300 (powArr 2300 dg[2]! (digit3 k 2)) (powArr 2300 dg[3]! (digit3 k 3))))

@[expose] def dElts (_ : Unit := ()) : Array (Array Nat) :=
  Array.ofFn (n := 81) fun k => dProd (dGens ()) k.val

@[expose] def dot3 (m k : Nat) : Nat :=
  (digit3 m 0 * digit3 k 0 + digit3 m 1 * digit3 k 1 + digit3 m 2 * digit3 k 2 +
    digit3 m 3 * digit3 k 3) % 3

@[expose] def rebuild (L : Array Level) (beta : Array Nat) : Array Nat := Id.run do
  let mut acc := idA 2300
  let mut accI := idA 2300
  for i in [0:6] do
    let k := L[i]!.pos[accI[beta[i]!]!]!
    acc := compA 2300 acc L[i]!.tr[k]!
    accI := compA 2300 L[i]!.trInv[k]! accI
  return acc

@[expose] def inD (E : Array (Array Nat)) (t : Array Nat) : Bool :=
  anyLt 81 fun k => eqA 2300 t E[k]!

@[expose] def coordOf (E : Array (Array Nat)) (g : Array Nat) (m s l : Nat) : Nat :=
  ((List.range 81).find? fun k =>
    dot3 m k == 0 && (E[k]!)[g[co2BaseArr[s]!]!]! == g[co2BaseArr[l]!]!).getD 81

@[expose] def relsOf (ys : Array (Array Nat)) : Array (Option (Nat × Array Nat)) :=
  #[none, some (0, ys[0]!), some (0, ys[1]!), some (0, ys[2]!), none, some (4, ys[3]!)]

@[expose] def leaves (L : Array Level) (ys : Array (Array Nat)) : List (Array Nat) :=
  dsearch 2300 L co2BaseArr (relsOf ys) (fun a => ys.all fun y => commA 2300 a y) 6 0
    (idA 2300) (idA 2300)

@[expose] def qCheck (_ : Unit := ()) : Bool :=
  let L := levels ()
  let gs := qGens2 ()
  let c := qCert2 ()
  enumOK 2300 gs co2E81.qKeys c && c.pts.size == 729 &&
    allLt gs.size fun k => inP L gs[k]!

@[expose] def dCheck (_ : Unit := ()) : Bool :=
  let L := levels ()
  let dg := dGens ()
  let E := dElts ()
  dg.size == 4 &&
  allLt 4 (fun i => validA 2300 dg[i]! && inP L dg[i]! &&
    eqA 2300 (powArr 2300 dg[i]! 3) (idA 2300)) &&
  allLt 4 (fun i => allLt 4 fun j => commA 2300 dg[i]! dg[j]!) &&
  allLt 81 (fun k => allLt 81 fun k' => k == k' || !(eqA 2300 E[k]! E[k']!))

@[expose] def fusCheck (_ : Unit := ()) : Bool :=
  let L := levels ()
  let c := qCert2 ()
  let E := dElts ()
  let hs := hGens ()
  hs.size == 16 && allLt 16 (fun i => validA 2300 hs[i]! && inP L hs[i]!) &&
  c.pts.size == 729 &&
  allLt 729 fun k =>
    let t := c.pts[k]!
    !(eqA 2300 (powArr 2300 t 3) (idA 2300)) || eqA 2300 t (idA 2300) || inD E t ||
      anyLt 16 fun i => inD E (conjA 2300 hs[i]! t)

@[expose] def hypG (_ : Unit := ()) : Array (Array Nat) := hypTuples.map (rebuild (levels ()))

@[expose] def hypC (_ : Unit := ()) : Array (Array Nat) :=
  ((hypG ()).zip hypFuncs).map fun gm => relPairs.map fun p => coordOf (dElts ()) gm.1 gm.2 p.1 p.2

@[expose] def hypY (_ : Unit := ()) : Array (Array (Array Nat)) :=
  ((hypG ()).zip (hypC ())).map fun gc => gc.2.map fun k => conjInvA 2300 gc.1 (dElts ())[k]!

@[expose] def hypCheck (_ : Unit := ()) : Bool :=
  let L := levels ()
  let G := hypG ()
  let C := hypC ()
  let Y := hypY ()
  G.size == 40 && C.size == 40 && Y.size == 40 &&
  parLt 40 8 (fun j => validA 2300 G[j]! && inP L G[j]! && (C[j]!).size == 4 &&
    (Y[j]!).size == 4 &&
    allLt 4 (fun t => decide ((C[j]!)[t]! < 81) && validA 2300 (Y[j]!)[t]! &&
      ((Y[j]!)[t]!)[co2BaseArr[(relPairs[t]!).1]!]! == co2BaseArr[(relPairs[t]!).2]!) &&
    decide ((leaves L Y[j]!).length ≤ 162)) &&
  decide ((leaves L Y[4]!).length ≤ 81) &&
  allLt 81 (fun m => m == 0 || anyLt 40 fun j => allLt 4 fun t => dot3 m (C[j]!)[t]! == 0)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T
