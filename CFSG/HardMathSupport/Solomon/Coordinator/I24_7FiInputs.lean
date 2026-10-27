module

public import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiHexP
public import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiHexSA
public import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiHexSB
public import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiHexSC
public import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
public import CFSG.Monster.B.Fischer.InducedData
public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.RankThree.Native.PermEnumeration
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiHexP
public meta import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiHexSA
public meta import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiHexSB
public meta import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiHexSC
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
public meta import CFSG.Monster.B.Fischer.InducedData
public meta import CFSG.RankThree.PartOne.KS.PKit
public meta import CFSG.RankThree.Native.PermEnumeration
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.RankThree.PartOne.KS.PKitLines
public import CFSG.RankThree.PartOne.KS.PKitLines
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer

@[expose] def fi22CoverP0Gens : Array (Array ℕ) :=
  Array.ofFn (n := 9) fun j => hexTable3 3510 (3510 * j.val) fi22CoverHexP

@[expose] def fi22CoverHexS : String := fi22CoverHexSA ++ fi22CoverHexSB ++ fi22CoverHexSC

@[expose] def fi22CoverS : Array (Array ℕ) :=
  Array.ofFn (n := 20) fun j => hexTable3 3510 (3510 * j.val) fi22CoverHexS

@[expose] def fi22CoverWords : Array (List ℤ) :=
    #[[], [], [], [-1, -3, -1, 2, 1, 3, 1], [-1, -2, 4, 2, 1], [-1, -1, 5, 1, 1], [-1, -2, 6, 2,
    1], [-1, -2, 7, 2, 1], [-1, -2, -1, 8, 5, 1], [-4, -9, 4, 9, 4], [-7, 10, 7], [-8, -9, 7, 9,
    8], [-4, -8, -6, 9, 12, 5, 4], [-13, 7, 13], [-2, -3, 4, 3, 2], [-9, -15, -6, 11, 5, 15],
    [-13, -10, 16, 6, 5], [-11, -17, -17, -14, 11, 17, 17, 14], [-17, -17, 18, 17, 17], [-18,
    -18, -17, -19, -17, 18, 17, 14, 11]]

@[expose] def fi22CoverBase : List (Fin 3510) := [0, 1, 2, 3, 4, 6]

@[expose] def fi22CoverBaseArr : Array ℕ := (fi22CoverBase.map Fin.val).toArray

@[expose] def fi22CoverN5 : Array ℕ := fi22CoverS[0]!

@[expose] def fi22CoverN4 : Array ℕ := fi22CoverS[1]!

@[expose] def fi22CoverN4' : Array ℕ := fi22CoverS[2]!

@[expose] def fi22CoverEvalWord (w : List ℤ) : Array ℕ :=
  wordA 3510 fi22CoverP0Gens (rawInvs 3510 fi22CoverP0Gens) w

@[expose] def fi22CoverE5 : Array (Array ℕ) :=
  #[fi22CoverEvalWord [1], fi22CoverEvalWord [4], fi22CoverEvalWord [7],
    fi22CoverEvalWord [8, 6], fi22CoverEvalWord [6, 8]]

@[expose] def fi22CoverQ4 : Array (Array ℕ) :=
  #[fi22CoverEvalWord [1], fi22CoverEvalWord [2], fi22CoverEvalWord [4],
    fi22CoverEvalWord [7]]

@[expose] def fi22CoverKeys : List ℕ := fi22BaseArr.toList

@[expose] def fi22CoverP0Cert (_ : Unit := ()) : ArrCert :=
  enumBfs 3510 fi22CoverP0Gens fi22CoverKeys 19700

@[expose] def fi22CoverE5Cert (_ : Unit := ()) : ArrCert :=
  enumBfs 3510 fi22CoverE5 fi22CoverKeys 260

@[expose] def fi22CoverQ4Cert (_ : Unit := ()) : ArrCert :=
  enumBfs 3510 fi22CoverQ4 fi22CoverKeys 100

@[expose] def fi22CoverElemOK (G : Array (Array ℕ)) : Bool :=
  allLt G.size fun i =>
    !(eqA 3510 G[i]! (idA 3510)) && eqA 3510 (powArr 3510 G[i]! 3) (idA 3510) &&
      allLt G.size fun j => commA 3510 G[i]! G[j]!

@[expose] def fi22CoverMemOK (G : Array (Array ℕ)) (c : ArrCert) : Bool :=
  allLt G.size fun i => c.pts.toList.any (eqA 3510 G[i]!)

@[expose] def fi22CoverNormOK (n : Array ℕ) (G : Array (Array ℕ)) (c : ArrCert) : Bool :=
  allLt G.size fun i =>
    c.pts.toList.any (fun pt => eqA 3510 (compA 3510 n G[i]!) (compA 3510 pt n)) &&
      c.pts.toList.any (fun pt => eqA 3510 (compA 3510 G[i]! n) (compA 3510 n pt))

@[expose] def fi22CoverCheck (_ : Unit := ()) : Bool :=
  let P0c := fi22CoverP0Cert ()
  let E5c := fi22CoverE5Cert ()
  let Q4c := fi22CoverQ4Cert ()
  let L := rawLevels 3510 fi22StrongArrs fi22BaseArr
  caseChainOK3 3510 fi22CoverS fi22CoverBaseArr fi22CoverWords fi22CoverN5 fi22CoverN4
      fi22CoverN4' &&
    (rawOrbitSizes 3510 fi22CoverS fi22CoverBaseArr == [3510, 2816, 567, 720, 8, 2]) &&
    validA 3510 fi22CoverN5 && validA 3510 fi22CoverN4 && validA 3510 fi22CoverN4' &&
    siftA 3510 L fi22BaseArr 0 fi22CoverN5 && siftA 3510 L fi22BaseArr 0 fi22CoverN4 &&
    siftA 3510 L fi22BaseArr 0 fi22CoverN4' &&
    allLt fi22CoverP0Gens.size (fun k => siftA 3510 L fi22BaseArr 0 fi22CoverP0Gens[k]!) &&
    enumOK 3510 fi22CoverP0Gens fi22CoverKeys P0c && (P0c.pts.size == 19683) &&
    enumOK 3510 fi22CoverE5 fi22CoverKeys E5c && (E5c.pts.size == 243) &&
    enumOK 3510 fi22CoverQ4 fi22CoverKeys Q4c && (Q4c.pts.size == 81) &&
    fi22CoverElemOK fi22CoverE5 && fi22CoverElemOK fi22CoverQ4 &&
    fi22CoverMemOK fi22CoverE5 P0c && fi22CoverMemOK fi22CoverQ4 P0c &&
    fi22CoverNormOK fi22CoverN5 fi22CoverE5 E5c && fi22CoverNormOK fi22CoverN4 fi22CoverQ4 Q4c &&
    fi22CoverNormOK fi22CoverN4' fi22CoverQ4 Q4c

end CFSG.HardMathSupport.Solomon.Coordinator
