module

public import CFSG.Quasithin.Background.G2UClosure
public meta import CFSG.Quasithin.Background.G2UClosure
public import Certificates.Data.CFSGNative.KGroups.Sp6G22
public meta import Certificates.Data.CFSGNative.KGroups.Sp6G22
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp62Local

open CFSG.KGroups.Sp6 CFSG.Quasithin.G2U

@[expose] def validB (c : List ℕ) : Bool :=
  c.length == 6 && c.all fun x => decide (x < 64)

@[expose] def invC (c : List ℕ) : List ℕ :=
  (List.range 6).map fun k => ((List.range 64).find? fun y => mulVecC c y == 2 ^ k).getD 0

@[expose] def isoB (c : List ℕ) : Bool :=
  validB c && (List.range 6).all fun i => (List.range 6).all fun j =>
    bf (c.getD i 0) (c.getD j 0) == decide (i + 3 = j ∨ j + 3 = i)

@[expose] def genB (c : List ℕ) : Bool :=
  isoB c && mulC c (invC c) == oneC && mulC (invC c) c == oneC

@[expose] def conjC (g x : List ℕ) : List ℕ := mulC g (mulC x (invC g))

@[expose] def commB (x y : List ℕ) : Bool := mulC x y == mulC y x

@[expose] def cubeB (x : List ℕ) : Bool := mulC x (mulC x x) == oneC

@[expose] def tabOf (gens : List (List ℕ)) (n : ℕ) : Array (List ℕ) :=
  build oneC mulC gens (bfsParents oneC mulC gens n)

@[expose] def inTab (tab : Array (List ℕ)) (c : List ℕ) : Bool := tab.contains c

@[expose] def tabCheck (gens : List (List ℕ)) (n : ℕ) (P : Array (List ℕ) → Bool) : Bool :=
  let tab := tabOf gens n
  gens.all genB && tab.size == n && closedCheck mulC gens tab && distinctCheck tab &&
    allCheck validB tab && P tab

@[expose] def cW0 : List ℕ := [8, 2, 4, 9, 16, 32]

@[expose] def cW1 : List ℕ := [1, 16, 4, 8, 18, 32]

@[expose] def cW2 : List ℕ := [1, 2, 32, 8, 16, 36]

@[expose] def cSg : List ℕ := [2, 4, 1, 16, 32, 8]

@[expose] def cTau : List ℕ := [2, 1, 4, 16, 8, 32]

@[expose] def cIo : List ℕ := [8, 2, 4, 1, 16, 32]

@[expose] def cGD : List ℕ := [60, 58, 57, 35, 21, 14]

@[expose] def cGu : List ℕ := [14, 21, 35, 57, 58, 60]

@[expose] def cZ : List ℕ := [8, 16, 32, 9, 18, 36]

@[expose] def cZ2 : List ℕ := [9, 18, 36, 1, 2, 4]

@[expose] def cBeta : List ℕ := [8, 18, 4, 9, 2, 32]

@[expose] def cGamma : List ℕ := [1, 16, 36, 8, 18, 4]

@[expose] def cA : List ℕ := [32, 2, 8, 4, 16, 1]

@[expose] def cB : List ℕ := [36, 8, 16, 56, 53, 62]

@[expose] def gensT : List (List ℕ) := [cW0, cW1, cW2, cSg]

@[expose] def gensB : List (List ℕ) := [cW0, cW1, cW2]

@[expose] def gensE : List (List ℕ) := [cBeta, cGamma, cSg]

@[expose] def gensD : List (List ℕ) := [cZ, cSg]

@[expose] def gensN : List (List ℕ) := [cW0, cW1, cW2, cSg, cTau, cIo]

@[expose] def gensWD : List (List ℕ) := [cW0, cW1, cW2, cSg, cTau, cIo, cGD]

@[expose] def gensWL : List (List ℕ) := [cW0, cW1, cW2, cSg, cTau, cIo, cGu]

@[expose] def gensV : List (List ℕ) := [cA, cB]

@[expose] def inZ (x : List ℕ) : Bool := x == oneC || x == cZ || x == cZ2

@[expose] def inZc (u v : List ℕ) : Bool := u == v || u == mulC v cZ || u == mulC v cZ2

@[expose] def actNe (tabE : Array (List ℕ)) (g h : List ℕ) : Bool :=
  tabE.toList.any fun x => !(inZc (conjC g x) (conjC h x))

@[expose] def chkT : Bool := tabCheck gensT 81 fun _ => true

@[expose] def propB1 (_ : Array (List ℕ)) : Bool := gensB.all (inTab (tabOf gensT 81))

@[expose] def propB2 (tabB : Array (List ℕ)) : Bool := allCheck cubeB tabB

@[expose] def propB3 (tabB : Array (List ℕ)) : Bool :=
  allCheck (fun x => gensB.all (commB x)) tabB

@[expose] def propB4 (tabB : Array (List ℕ)) : Bool :=
  gensN.all fun g => genB g && gensB.all fun x => inTab tabB (conjC g x)

@[expose] def propB (tabB : Array (List ℕ)) : Bool :=
  propB1 tabB && (propB2 tabB && (propB3 tabB && propB4 tabB))

@[expose] def chkB : Bool := tabCheck gensB 27 propB

@[expose] def propE1 (_ : Array (List ℕ)) : Bool := gensE.all (inTab (tabOf gensT 81))

@[expose] def propE2 (tabE : Array (List ℕ)) : Bool := allCheck cubeB tabE

@[expose] def propE3 (_ : Array (List ℕ)) : Bool := !(commB cSg cBeta)

@[expose] def propE4 (_ : Array (List ℕ)) : Bool := gensE.all (commB cZ)

@[expose] def propE5 (tabE : Array (List ℕ)) : Bool := inTab tabE cZ && genB cZ

@[expose] def propE6 (_ : Array (List ℕ)) : Bool := cubeB cZ

@[expose] def propE7 (_ : Array (List ℕ)) : Bool := cZ != oneC

@[expose] def propE8 (_ : Array (List ℕ)) : Bool := cZ2 == mulC cZ cZ

@[expose] def propE9 (tabE : Array (List ℕ)) : Bool :=
  allCheck (fun x => !(gensE.all (commB x)) || inZ x) tabE

@[expose] def propE10 (tabE : Array (List ℕ)) : Bool :=
  [cW0, cGu].all fun g => genB g && gensE.all (fun x => inTab tabE (conjC g x)) &&
    commB g cZ && cubeB g

@[expose] def propE11 (tabE : Array (List ℕ)) : Bool := actNe tabE cGu oneC

@[expose] def propE12 (tabE : Array (List ℕ)) : Bool := actNe tabE cW0 oneC

@[expose] def propE13 (tabE : Array (List ℕ)) : Bool := actNe tabE cW0 cGu

@[expose] def propE14 (tabE : Array (List ℕ)) : Bool :=
  genB (invC cGu) && actNe tabE cW0 (invC cGu)

@[expose] def propE (tabE : Array (List ℕ)) : Bool :=
  propE1 tabE && (propE2 tabE && (propE3 tabE && (propE4 tabE && (propE5 tabE && (
  propE6 tabE && (propE7 tabE && (propE8 tabE && (propE9 tabE && (propE10 tabE && (
  propE11 tabE && (propE12 tabE && (propE13 tabE && propE14 tabE))))))))))))

@[expose] def chkE : Bool := tabCheck gensE 27 propE

@[expose] def propD1 (_ : Array (List ℕ)) : Bool := gensD.all (inTab (tabOf gensE 27))

@[expose] def propD2 (tabD : Array (List ℕ)) : Bool := allCheck cubeB tabD

@[expose] def propD3 (tabD : Array (List ℕ)) : Bool :=
  allCheck (fun x => gensD.all (commB x)) tabD

@[expose] def propD4 (tabD : Array (List ℕ)) : Bool :=
  allCheck (fun y => !(gensT.all (commB y)) || inZ y) tabD

@[expose] def propD5 (tabD : Array (List ℕ)) : Bool :=
  genB cGD && gensD.all fun x => inTab tabD (conjC cGD x)

@[expose] def propD (tabD : Array (List ℕ)) : Bool :=
  propD1 tabD && (propD2 tabD && (propD3 tabD && (propD4 tabD && propD5 tabD)))

@[expose] def chkD : Bool := tabCheck gensD 9 propD

@[expose] def propWD1 (tabW : Array (List ℕ)) : Bool := gensV.all (inTab tabW)

@[expose] def propWD2 (tabW : Array (List ℕ)) : Bool := gensWL.all (inTab tabW)

@[expose] def propWD3 (tabW : Array (List ℕ)) : Bool :=
  allCheck (fun x => !(gensV.all (commB x)) || x == oneC) tabW

@[expose] def propWD4 (tabW : Array (List ℕ)) : Bool :=
  allCheck (fun x => !(gensT.all (commB x)) || inTab (tabOf gensT 81) x) tabW

@[expose] def propWD (tabW : Array (List ℕ)) : Bool :=
  propWD1 tabW && (propWD2 tabW && (propWD3 tabW && propWD4 tabW))

@[expose] def chkWD : Bool := tabCheck gensWD 51840 propWD

@[expose] def propWL (tabW' : Array (List ℕ)) : Bool := gensWD.all (inTab tabW')

@[expose] def chkWL : Bool := tabCheck gensWL 51840 propWL

@[expose] def propV1 (tabV : Array (List ℕ)) : Bool := gensT.all (inTab tabV)

@[expose] def propV2 (tabV : Array (List ℕ)) : Bool :=
  gensWD.all fun g => genB g && gensV.all fun x => inTab tabV (conjC g x)

@[expose] def propV (tabV : Array (List ℕ)) : Bool := propV1 tabV && propV2 tabV

@[expose] def chkV : Bool := tabCheck gensV 25920 propV

@[expose] def letterC (l : ℕ × Bool) : List ℕ :=
  if l.1 = 0 then (if l.2 then cA else invC cA) else (if l.2 then cB else invC cB)

@[expose] def evalW (w : List (ℕ × Bool)) : List ℕ :=
  w.foldr (fun l acc => mulC (letterC l) acc) oneC

@[expose] def relWords : List (List (ℕ × Bool)) :=
  [[(0, true), (0, true)],
    List.replicate 5 (1, true),
    (List.replicate 9 [(0, true), (1, true)]).flatten,
    (List.replicate 3 [(0, true), (1, true), (0, false), (1, false)]).flatten,
    (List.replicate 2 [(0, true), (1, true), (0, true), (1, true), (0, false), (1, false),
      (0, false), (1, false)]).flatten]

@[expose] def chkRel : Bool :=
  genB cA && genB cB && !(commB cA cB) && relWords.all fun w => evalW w == oneC

@[expose] def qv (x : ℕ) : Bool :=
  (x.testBit 0 ^^ (x.testBit 0 && x.testBit 3) ^^ x.testBit 3) ^^
  (x.testBit 1 ^^ (x.testBit 1 && x.testBit 4) ^^ x.testBit 4) ^^
  (x.testBit 2 ^^ (x.testBit 2 && x.testBit 5) ^^ x.testBit 5)

@[expose] def qbits (M : List ℕ) : ℕ :=
  (if qv (M.getD 0 0) then 1 else 0) + 2 * (if qv (M.getD 1 0) then 1 else 0) +
  4 * (if qv (M.getD 2 0) then 1 else 0) + 8 * (if qv (M.getD 3 0) then 1 else 0) +
  16 * (if qv (M.getD 4 0) then 1 else 0) + 32 * (if qv (M.getD 5 0) then 1 else 0)

@[expose] def cG1 : List ℕ := [1, 2, 4, 11, 19, 32]

@[expose] def vPairs : List (ℕ × List ℕ) :=
  [(9, [42, 28, 15, 23, 39, 62]), (11, [56, 30, 29, 7, 53, 46]),
    (13, [46, 56, 43, 51, 7, 30]), (15, [60, 58, 57, 35, 21, 14]),
    (18, [36, 9, 2, 4, 1, 16]), (19, [36, 1, 2, 4, 8, 16]),
    (22, [4, 9, 2, 32, 1, 16]), (23, [4, 1, 2, 32, 8, 16]),
    (25, [36, 16, 1, 4, 2, 8]), (26, [36, 8, 2, 4, 1, 16]),
    (29, [4, 16, 1, 32, 2, 8]), (30, [4, 8, 2, 32, 1, 16]),
    (36, [9, 18, 4, 1, 2, 32]), (37, [1, 18, 4, 8, 2, 32]),
    (38, [9, 2, 4, 1, 16, 32]), (41, [14, 60, 58, 57, 35, 21]),
    (43, [2, 32, 1, 16, 4, 8]), (44, [8, 18, 4, 1, 2, 32]),
    (46, [8, 2, 4, 1, 16, 32]), (50, [60, 21, 57, 35, 47, 14]),
    (51, [32, 1, 2, 4, 8, 16]), (52, [35, 58, 57, 60, 21, 14]),
    (53, [1, 16, 4, 8, 18, 32]), (57, [31, 47, 57, 60, 58, 14]),
    (58, [32, 8, 2, 4, 1, 16]), (60, [8, 16, 4, 1, 18, 32])]

@[expose] def vOf (b : ℕ) : List ℕ := (vPairs.lookup b).getD oneC

@[expose] def dcCheck : Bool :=
  let hs : Std.HashSet (List ℕ) := Std.HashSet.ofList (tabOf gensWD 51840).toList
  genB cG1 && vPairs.all (fun p => hs.contains p.2) &&
    (spCount 64 fun x =>
      if qbits x == 63 then !hs.contains x
      else !hs.contains (mulC (mulC x (vOf (qbits x))) (invC cG1))) == 0

end CFSG.AGLEmbedding.KFactProofs.Sp62Local
