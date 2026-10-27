module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcO8Defs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylFrameData
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.HeldB.Common
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizerData
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFusion
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
public import CFSG.RankThree.Native.PermEnumeration

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ExcO8W

open CFSG.ComponentClassification.RankTwoClassical.ExcO8
open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.HeldB CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.OmegaEight.Weyl

@[expose] def refls : List (Equiv.Perm (Fin 240)) :=
  (List.range 240).map fun r => permOrId 240 reflArrs[r]!

@[expose] def okW (w : List ℤ) : Bool :=
  decide (w.length % 2 = 0) && w.all fun z => decide (z ≠ 0) && decide (z.natAbs ≤ 240)

@[expose] def zC : Equiv.Perm (Fin 240) := permOrId 240 negArr

@[expose] def zs : List (Equiv.Perm (Fin 240)) := [zC]

@[expose] def tWords : List (List ℤ) :=
  [[1, 2], [5, 6], [9, 10], [13, 14], [17, 18], [21, 22], [25, 26], [2, 54], [6, 34], [90, 110],
    [94, 106], [2, 90], [14, 42, 66, 86]]

@[expose] def tGens : List (Equiv.Perm (Fin 240)) := tWords.map fun w => tab (evalCodes refls w)

@[expose] def tQ : RawSchreierDatum 240 :=
  certificate (by decide) tGens
    [[3, 2], [4, 2], [12, 8], [4, 3], [5, 4], [6, 4], [6, 5], [7, 5], [7, 6]]
    #v[0, 1, 4, 8, 12, 16, 20] (by decide)

@[expose] def tRepWords : List (List ℤ) :=
  [[1], [2], [4], [8], [9], [12], [13], [10, 1], [11, 1], [10, 2], [11, 2], [11, 3], [13, 4],
    [10, 8], [11, 8], [11, 9], [13, 12], [3, 2, 1], [4, 2, 1], [5, 4, 1], [6, 4, 1], [10, 8, 1],
    [11, 8, 1], [12, 8, 1], [6, 4, 2], [7, 4, 2], [12, 6, 2], [11, 9, 2], [13, 12, 5], [11, 9, 8],
    [10, 3, 2, 1], [11, 3, 2, 1], [11, 10, 9, 2], [12, 7, 8, 6], [5, 4, 3, 2, 1], [6, 4, 3, 2, 1],
    [6, 5, 4, 2, 1], [7, 6, 5, 4, 3, 2, 1]]

@[expose] def tReps : List (Equiv.Perm (Fin 240)) := tRepWords.map fun w => tab (evalCodes tGens w)

@[expose] def fusion : List (ℕ × List ℤ) :=
  [(2, []), (2, [2, 30, 102, 110]), (2, [30, 57, 77, 85]), (2, [1, 2, 53, 61, 86, 94, 132, 133]),
    (2, [30, 33, 89, 93, 148, 149]), (2, [53, 74, 81, 97, 126, 133]),
    (1, [14, 85, 118, 148, 153, 174]), (4, [89, 109, 164, 165]), (4, [5, 6, 90, 98, 162, 167]),
    (4, [1, 17, 29, 46, 57, 85, 115, 118]), (4, [14, 45, 62, 86, 115, 118]),
    (4, [18, 49, 66, 74, 156, 157]), (4, [1, 2, 6, 33, 38, 41, 66, 110]),
    (1, [1, 21, 49, 54, 130, 135]), (1, [30, 54, 90, 97, 138, 161]),
    (1, [1, 6, 10, 41, 86, 93, 146, 151]), (1, [6, 46, 77, 97, 118, 141]), (1, []), (1, [74, 85]),
    (1, [2, 57, 77, 110]), (1, [2, 57, 81, 106]), (4, []), (4, [2, 18, 37, 102]),
    (4, [54, 90, 146, 176]), (1, [6, 37, 81, 106]), (1, [1, 2, 30, 38, 77, 81, 82, 105]),
    (4, [1, 5, 26, 45, 130, 144, 156, 173]), (4, [1, 2, 10, 41, 69, 70, 73, 101]),
    (4, [2, 30, 62, 66, 74, 110]), (1, [1, 6, 37, 41, 50, 66, 171, 174]), (3, [90, 109, 169, 176]),
    (3, [2, 33, 89, 97, 148, 149]), (4, [2, 30, 102, 110]),
    (3, [1, 2, 10, 13, 121, 130, 171, 174]), (3, []), (3, [2, 6, 102, 106]), (3, [6, 57, 77, 81]),
    (0, [])]

@[expose] def x24 : Equiv.Perm (Fin 240) := tab (evalCodes tGens [3, 2, 1])

@[expose] def x60 : Equiv.Perm (Fin 240) := tab (evalCodes tGens [1])

@[expose] def x4 : Equiv.Perm (Fin 240) := tab (evalCodes tGens [5, 4, 3, 2, 1])

@[expose] def x8 : Equiv.Perm (Fin 240) := tab (evalCodes tGens [10, 8, 1])

@[expose] def xs : List (Equiv.Perm (Fin 240)) := [x24, x60, x4, x8]

@[expose] def xsFix : List ℕ := [24, 60, 4, 8]

@[expose] def xsMin : List ℕ := [2, 4, 4, 8]

@[expose] def s24Words : List (List ℤ) :=
  [[2], [3], [6], [5], [7], [9], [4], [11], [12]]

@[expose] def s24Gens : List (Equiv.Perm (Fin 240)) :=
  s24Words.map fun w => tab (evalCodes tGens w)

@[expose] def s24Q : RawSchreierDatum 240 :=
  certificate (by decide) s24Gens
    [[2, 1], [3, 1], [6, 9, 6], [3, 2], [4, 2], [9, 8, 9], [4, 3], [5, 3]]
    #v[0, 1, 4, 8, 12, 16, 20] (by decide)

@[expose] def r24Words : List (List ℤ) :=
  [[1], [3], [6], [8], [9], [2, 1], [8, 1], [8, 2], [4, 3], [5, 3], [8, 6], [3, 2, 1], [8, 2, 1],
    [9, 2, 1], [4, 3, 1], [5, 3, 1], [7, 3, 1], [9, 3, 1], [8, 6, 1], [5, 4, 3], [6, 4, 3],
    [6, 5, 3], [9, 5, 3], [7, 6, 3], [4, 3, 2, 1], [5, 3, 2, 1], [9, 2, 9, 1], [7, 5, 4, 3],
    [9, 6, 9, 6], [9, 8, 9, 6], [9, 8, 9, 8], [5, 4, 3, 2, 1], [9, 5, 3, 2, 1], [7, 5, 4, 3, 1],
    [9, 8, 9, 6, 1], [9, 2, 9, 8, 1], [9, 8, 9, 8, 1], [7, 6, 5, 4, 3], [9, 6, 9, 8, 6],
    [9, 8, 9, 8, 6], [7, 5, 4, 3, 2, 1], [9, 4, 9, 3, 2, 1], [9, 5, 9, 3, 2, 1],
    [9, 8, 9, 8, 2, 1], [9, 8, 9, 8, 6, 1], [9, 8, 2, 9, 8, 1], [9, 6, 9, 6, 4, 3],
    [9, 6, 9, 6, 5, 3], [9, 8, 6, 9, 8, 6], [9, 6, 9, 8, 6, 2, 1], [9, 4, 9, 5, 4, 3, 2, 1],
    [9, 8, 6, 9, 8, 6, 2, 1], [9, 4, 6, 9, 6, 5, 4, 3]]

@[expose] def r24Reps : List (Equiv.Perm (Fin 240)) := r24Words.map (evalCodes s24Gens)

@[expose] def d24Data : String :=
  "2:5,86:0;1:1,41,42,53,116,117:1|1:1,41,42,53,116,117:1|2:6,158:0;1:1,41,42,53,116,117:1|1:29,30\
  ,97,98:1|2:1,53,82,90,119,173:0|2:17,53:0;1:1,41,42,53,116,117:1|1:29,30,97,98:1|1:29,30,97,98:1\
  |1:5,33,89,109:1|1:10,30,97,101:1|1:29,30,97,98:1|1:1,41,42,53,116,117:1|1:29,30,97,98:1|3:13,42\
  ,53,81,82,169:0|1:5,33,89,109:1|1:10,30,97,101:1|1:5,33,89,109:1|1:5,33,89,109:1|1:29,30,97,98:1\
  |1:1,41,42,53,116,117:1|1:5,33,89,109:1|1:10,30,97,101:1|3:1,2,54,66,90,126,151,176:0|1:5,33,89,\
  109:1|1:5,33,89,109:1|1:10,30,97,101:1|||2:2,120:0;1:1,41,42,53,116,117:1|1:53,54,93,94:1|1:29,3\
  0,97,98:1|1:1,41,42,53,116,117:1|2:1,66,89,122:0|2:33,69:0;1:1,41,42,53,116,117:1|1:53,54,93,94:\
  1|1:29,30,97,98:1|1:29,30,97,98:1|3:5,176:0;1:1,41,42,53,116,117:1|1:29,30,97,98:1|1:29,30,97,98\
  :1|2:2,81:0;1:1,41,42,53,116,117:1|1:5,33,89,109:1|1:10,30,97,101:1|1:29,30,97,98:1|1:29,30,97,9\
  8:1|1:29,30,97,98:1|1:5,33,89,109:1|1:10,30,97,101:1|1:29,30,97,98:1|1:29,30,97,98:1||1:29,30,97\
  ,98:1|2:53,156:0;1:1,41,42,53,116,117:1"

@[expose] def d24 : List (List (ℕ × List ℤ × ℕ)) := parseDerivs d24Data

@[expose] def s60Words : List (List ℤ) :=
  [[4], [7], [5], [3], [6], [8], [10], [11], [12]]

@[expose] def s60Gens : List (Equiv.Perm (Fin 240)) :=
  s60Words.map fun w => tab (evalCodes tGens w)

@[expose] def s60Q : RawSchreierDatum 240 :=
  certificate (by decide) s60Gens
    [[2, 1], [4, 1], [9, 6], [3, 1], [3, 2], [5, 2]]
    #v[0, 1, 4, 8, 12, 16, 20] (by decide)

@[expose] def r60Words : List (List ℤ) :=
  [[1], [4], [6], [7], [8], [9], [2, 1], [3, 1], [4, 1], [7, 4], [8, 4], [7, 6], [8, 6], [9, 6],
    [3, 2, 1], [4, 2, 1], [6, 2, 1], [4, 3, 1], [6, 3, 1], [5, 4, 1], [9, 4, 2], [9, 5, 2],
    [9, 6, 2], [8, 7, 4], [4, 3, 2, 1], [5, 3, 2, 1], [7, 6, 3, 1], [8, 6, 5, 1], [6, 1, 6, 1],
    [9, 1, 6, 1], [6, 2, 6, 1], [6, 3, 6, 1], [6, 4, 6, 1], [9, 6, 5, 2], [9, 5, 6, 2],
    [6, 4, 6, 4], [5, 4, 3, 2, 1], [6, 5, 3, 2, 1], [6, 4, 6, 4, 1], [7, 6, 1, 6, 1],
    [8, 6, 1, 6, 1], [7, 6, 4, 6, 4], [8, 6, 4, 6, 4], [9, 6, 4, 6, 4], [6, 4, 6, 3, 2, 1],
    [6, 5, 6, 3, 2, 1], [6, 4, 6, 4, 2, 1], [6, 4, 6, 4, 3, 1], [6, 4, 1, 6, 4, 1],
    [6, 4, 2, 6, 4, 1], [6, 4, 3, 6, 4, 1], [6, 4, 6, 4, 3, 2, 1], [7, 6, 4, 1, 6, 4, 1],
    [8, 6, 4, 1, 6, 4, 1], [9, 6, 4, 6, 5, 4, 2], [6, 4, 6, 5, 4, 3, 2, 1],
    [6, 5, 4, 6, 4, 3, 2, 1]]

@[expose] def r60Reps : List (Equiv.Perm (Fin 240)) := r60Words.map (evalCodes s60Gens)

@[expose] def d60Data : String :=
  "1:29,30,54,89,101,109:1|1:29,30,54,89,101,109:1|1:29,30,54,89,101,109:1|1:1,2,62,85:1|1:2,78:1|\
  1:29,30,54,89,101,109:1||||1:1,2,62,85:1|1:29,30,54,89,101,109:1|||1:29,30,54,89,101,109:1|||1:2\
  9,30,54,89,101,109:1||1:29,30,54,89,101,109:1||1:29,30,54,89,101,109:1|1:29,30,54,89,101,109:1|1\
  :29,30,54,89,101,109:1|1:1,2,62,85:1||||||1:29,30,54,89,101,109:1||||1:29,30,54,89,101,109:1|1:2\
  9,30,54,89,101,109:1||1:29,30,54,89,101,109:1|1:29,30,54,89,101,109:1||1:1,2,62,85:1|1:2,78:1|1:\
  1,2,62,85:1|1:2,78:1|1:29,30,54,89,101,109:1||||||||1:29,30,54,89,101,109:1|1:1,2,62,85:1|1:2,78\
  :1|1:29,30,54,89,101,109:1||"

@[expose] def d60 : List (List (ℕ × List ℤ × ℕ)) := parseDerivs d60Data

@[expose] def s4Words : List (List ℤ) :=
  [[4], [9], [7], [5], [3], [10], [8], [12]]

@[expose] def s4Gens : List (Equiv.Perm (Fin 240)) :=
  s4Words.map fun w => tab (evalCodes tGens w)

@[expose] def s4Q : RawSchreierDatum 240 :=
  certificate (by decide) s4Gens
    [[3, 1], [5, 1], [8, 7], [4, 1], [4, 3], [6, 3, 6, 3]]
    #v[0, 1, 4, 8, 12, 16, 20] (by decide)

@[expose] def r4Words : List (List ℤ) :=
  [[1], [2], [3], [5], [6], [7], [8], [3, 1], [4, 1], [6, 2], [6, 5], [7, 6], [8, 6], [3, 2, 1],
    [4, 2, 1], [4, 3, 1], [5, 3, 1], [7, 3, 1], [5, 4, 1], [7, 4, 1], [4, 3, 2], [5, 4, 3],
    [8, 5, 3], [6, 1, 2, 1], [2, 5, 2, 1], [7, 6, 4, 1], [8, 6, 4, 1], [8, 6, 5, 1], [7, 1, 7, 1],
    [8, 1, 7, 1], [7, 3, 7, 1], [7, 4, 7, 1], [5, 2, 3, 2], [5, 2, 5, 2], [6, 3, 6, 3],
    [6, 3, 6, 3, 1], [7, 1, 7, 6, 1], [8, 1, 7, 6, 1], [8, 4, 7, 6, 1], [6, 3, 6, 3, 2],
    [6, 5, 2, 5, 2], [6, 3, 6, 5, 3], [7, 6, 3, 6, 3], [8, 6, 3, 6, 3], [5, 4, 2, 3, 2, 1],
    [5, 3, 2, 5, 2, 1], [5, 4, 2, 5, 2, 1], [6, 3, 6, 4, 3, 1], [7, 6, 3, 7, 6, 3],
    [8, 6, 3, 7, 6, 3], [6, 3, 6, 4, 3, 2, 1], [6, 3, 6, 5, 4, 3, 1], [7, 6, 3, 6, 4, 3, 1],
    [6, 3, 6, 5, 2, 3, 2, 1], [7, 6, 3, 7, 6, 4, 3, 1], [6, 5, 2, 3, 6, 5, 3, 2],
    [6, 3, 6, 5, 2, 5, 4, 3, 2, 1]]

@[expose] def r4Reps : List (Equiv.Perm (Fin 240)) := r4Words.map (evalCodes s4Gens)

@[expose] def d4Data : String :=
  "||||||||||1:1,5,6,10,38,90:1|||1:1,5,6,10,38,90:1||||1:1,5,6,10,38,90:1|||1:1,5,6,10,38,90:1||1\
  :1,5,6,10,38,90:1||||1:1,5,6,10,38,90:1|1:1,5,6,10,38,90:1|||||||||1:1,5,6,10,38,90:1||1:1,5,6,1\
  0,38,90:1|1:1,5,6,10,38,90:1|||1:1,5,6,10,38,90:1|1:1,5,6,10,38,90:1||||||1:1,5,6,10,38,90:1|1:1\
  ,5,6,10,38,90:1||1:1,5,6,10,38,90:1||||"

@[expose] def d4 : List (List (ℕ × List ℤ × ℕ)) := parseDerivs d4Data

@[expose] def s8Words : List (List ℤ) :=
  [[12], [1], [11], [8], [13, 5]]

@[expose] def s8Gens : List (Equiv.Perm (Fin 240)) :=
  s8Words.map fun w => tab (evalCodes tGens w)

@[expose] def s8Q : RawSchreierDatum 240 :=
  certificate (by decide) s8Gens
    [[5, 5, 2], [5, 3, 5, 5, 3, 5, 2], [4, 1], [1, 3, 1], [3, 5, 5, 3, 2]]
    #v[0, 1, 4, 12, 20] (by decide)

@[expose] def r8Words : List (List ℤ) :=
  [[1], [2], [3], [4], [2, 1], [5, 1], [3, 2], [4, 2], [5, 2], [4, 3], [5, 5], [4, 2, 1],
    [4, 3, 2], [5, 5, 4], [5, 5, 2, 1], [5, 5, 4, 1], [5, 5, 4, 2], [5, 4, 5, 4], [4, 3, 1, 3, 1],
    [3, 5, 5, 4, 3, 1], [5, 3, 1, 5, 3, 1], [5, 1, 3, 5, 3, 1], [5, 4, 1, 5, 4, 1],
    [5, 5, 3, 5, 5, 3], [5, 5, 3, 5, 5, 3, 1], [5, 5, 3, 5, 5, 3, 2], [5, 5, 3, 5, 5, 4, 3],
    [5, 5, 3, 5, 3, 5, 3], [5, 5, 3, 5, 5, 3, 2, 1], [5, 5, 3, 5, 5, 1, 3, 1],
    [5, 5, 3, 5, 5, 4, 3, 2], [5, 3, 5, 3, 5, 3, 5, 3], [5, 5, 3, 5, 5, 1, 3, 2, 1],
    [5, 5, 3, 5, 5, 4, 3, 2, 1], [5, 5, 3, 5, 5, 4, 1, 3, 1], [5, 5, 3, 5, 3, 5, 1, 3, 1],
    [5, 5, 3, 5, 5, 4, 1, 3, 2, 1], [5, 3, 5, 3, 5, 3, 5, 3, 2, 1], [5, 3, 5, 3, 5, 3, 5, 1, 3, 1],
    [5, 3, 5, 3, 5, 3, 5, 4, 1, 3, 2, 1]]

@[expose] def r8Reps : List (Equiv.Perm (Fin 240)) := r8Words.map (evalCodes s8Gens)

@[expose] def d8Data : String :=
  "|||||1:17,38,53,110:1|||1:17,38,53,110:1|||||||1:17,38,53,110:1|1:17,38,53,110:1||||1:17,38,53,\
  110:1|1:17,38,53,110:1|||||||1:17,38,53,110:1|||||||||||"

@[expose] def d8 : List (List (ℕ × List ℤ × ℕ)) := parseDerivs d8Data

@[expose] def censusArrCheck : Bool :=
  (List.range 240).all (fun r => isInvA 240 reflArrs[r]! (invCand 240 reflArrs[r]!) &&
      isInvA 240 (invCand 240 reflArrs[r]!) reflArrs[r]!) &&
    isInvA 240 negArr (invCand 240 negArr) && isInvA 240 (invCand 240 negArr) negArr

@[expose] def censusChainCheck : Bool :=
  tQ.check && tQ.orderCertificate == 8192 && tWords.all okW &&
    s24Q.check && s24Q.orderCertificate == 4096 &&
      s24Gens.all (fun g => schreierPermEq (g * x24) (x24 * g)) &&
    s60Q.check && s60Q.orderCertificate == 2048 &&
      s60Gens.all (fun g => schreierPermEq (g * x60) (x60 * g)) &&
    s4Q.check && s4Q.orderCertificate == 2048 &&
      s4Gens.all (fun g => schreierPermEq (g * x4) (x4 * g)) &&
    s8Q.check && s8Q.orderCertificate == 1024 &&
      s8Gens.all (fun g => schreierPermEq (g * x8) (x8 * g))

@[expose] def censusCoverCheck : Bool :=
  repsOK 240 (listTables tGens) (listTables (tGens.map (·⁻¹))) (cosetOrderTables tQ 1 2)
      (tReps.map toTable) 600 &&
    (tReps.map toTable).all (ordTest 240 2) &&
    repsOK 240 (listTables s24Gens) (listTables (s24Gens.map (·⁻¹)))
      (cosetOrderTables s24Q 1 2) (r24Reps.map toTable) 600 &&
    (r24Reps.map toTable).all (ordTest 240 2) &&
    repsOK 240 (listTables s60Gens) (listTables (s60Gens.map (·⁻¹)))
      (cosetOrderTables s60Q 1 2) (r60Reps.map toTable) 600 &&
    (r60Reps.map toTable).all (ordTest 240 2) &&
    repsOK 240 (listTables s4Gens) (listTables (s4Gens.map (·⁻¹)))
      (cosetOrderTables s4Q 1 2) (r4Reps.map toTable) 600 &&
    (r4Reps.map toTable).all (ordTest 240 2) &&
    repsOK 240 (listTables s8Gens) (listTables (s8Gens.map (·⁻¹)))
      (cosetOrderTables s8Q 1 2) (r8Reps.map toTable) 600 &&
    (r8Reps.map toTable).all (ordTest 240 2)

@[expose] def censusFusionCheck : Bool :=
  fusion.length == tReps.length && xs.map fixNum == xsFix &&
    xs.all (fun x => ordTest 240 2 (toTable x) && !schreierPermEq x zC) &&
    (tReps.zip fusion).all (fun p =>
      if p.2.1 = 0 then schreierPermEq p.1 zC
      else
        let g := tab (evalCodes refls p.2.2)
        okW p.2.2 && decide (p.2.1 ≤ xs.length) &&
          schreierPermEq (g * p.1 * g⁻¹) (xs.getD (p.2.1 - 1) 1)) &&
    (tReps.zip (repSizes 240 (listTables tGens) (listTables (tGens.map (·⁻¹)))
      (tReps.map toTable) 600)).all (fun p =>
      (xsFix.zip xsMin).all fun q => fixNum p.1 != q.1 || decide (q.2 ≤ p.2))

@[expose] def censusDerivCheck : Bool :=
  d24.length == r24Reps.length && d60.length == r60Reps.length &&
    d4.length == r4Reps.length && d8.length == r8Reps.length &&
    (r24Reps.zip d24).all (fun p =>
      schreierPermEq p.1 x24 || derivCheck refls okW zs [] [x24, p.1] p.2) &&
    (r60Reps.zip d60).all (fun p =>
      schreierPermEq p.1 x60 || derivCheck refls okW zs [24] [x60, p.1] p.2) &&
    (r4Reps.zip d4).all (fun p =>
      schreierPermEq p.1 x4 || derivCheck refls okW zs [24, 60] [x4, p.1] p.2) &&
    (r8Reps.zip d8).all (fun p =>
      schreierPermEq p.1 x8 || derivCheck refls okW zs [24, 60, 4] [x8, p.1] p.2)

end CFSG.ComponentClassification.RankTwoClassical.ExcO8W
