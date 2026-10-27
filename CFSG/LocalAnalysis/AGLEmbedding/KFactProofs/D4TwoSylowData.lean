module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.D4TwoArr
public meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.D4TwoArr
public meta import CFSG.Open.QuasithinDefs
public meta import CFSG.Quasithin.Recognition.CertF8
public meta import CFSG.Quasithin.Recognition.CertTrialityModel

public section

namespace CFSG.AGLEmbedding.D4Two

open CFSG.Quasithin

@[expose] def wordA : List ℕ := [5, 10, 17, 16, 11, 17, 9, 17, 16, 4]

@[expose] def wordB : List ℕ := [12, 1, 17, 14, 17, 15, 3, 16, 5, 17, 16, 7]

@[expose] def bfsPar : List (ℕ × Bool) :=
  [(0, true), (0, false), (1, true), (1, false), (2, true), (2, false), (3, false), (4, true),
   (4, false), (5, true), (5, false), (6, true), (7, true), (7, false), (8, true), (8, false),
   (9, true), (10, false), (11, false), (12, false), (13, true), (13, false), (14, true),
   (15, false), (16, false), (17, false), (18, true), (18, false), (19, true), (20, false),
   (21, false), (22, false), (23, false), (24, true), (24, false), (25, true), (26, false),
   (27, true), (27, false), (28, true), (29, false), (30, true), (31, true), (31, false),
   (32, true), (33, false), (34, true), (34, false), (35, true), (36, false), (37, true),
   (38, false), (39, false), (40, false), (41, false), (42, false), (43, true), (43, false),
   (44, true), (45, false), (46, true), (47, false), (48, false), (49, false), (50, false),
   (51, false), (52, false), (54, false), (56, false), (57, false), (58, false), (59, false),
   (60, false), (61, false), (62, false), (64, false), (66, false), (70, false), (72, false),
   (74, false)]

@[expose] def genA : Array GF8 := wordArr wordA

@[expose] def genB : Array GF8 := wordArr wordB

@[expose] def bfsStep (A B : Array GF8) (acc : List (Array GF8)) (p : ℕ × Bool) :
    List (Array GF8) :=
  acc ++ [mulArr (acc.getD p.1 oneArr) (if p.2 then A else B)]

@[expose] def bfsElems (A B : Array GF8) (par : List (ℕ × Bool)) : List (Array GF8) :=
  par.foldl (bfsStep A B) [oneArr]

@[expose] def sylowElems : List (Array GF8) := bfsElems genA genB bfsPar

@[expose] def cube1 (x : Array GF8) : Bool := mulArr x (mulArr x x) == oneArr

@[expose] def commutes (x y : Array GF8) : Bool := mulArr x y == mulArr y x

@[expose] def rankCheck (Xs : List (Array GF8)) : Bool :=
  let Om := Xs.filter cube1
  Om.all fun x =>
    let cx := Om.filter (commutes x)
    let sx := [oneArr, x, mulArr x x]
    x == oneArr || cx.all fun y =>
      sx.contains y ||
        let sy := [oneArr, y, mulArr y y]
        let P := sx.flatMap fun u => sy.map fun v => mulArr u v
        (cx.filter (commutes y)).all fun z => P.contains z

@[expose] def d4SylowCheck : Bool :=
  let Xs := sylowElems
  Xs.length == 81 && decide Xs.Nodup &&
    Xs.all (fun x => Xs.contains (mulArr x genA) && Xs.contains (mulArr x genB)) && rankCheck Xs

end CFSG.AGLEmbedding.D4Two
