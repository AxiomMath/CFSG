module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaGrpDefs

public section

namespace CFSG.AGLEmbedding.R3.AlphaJ3

open CFSG.SectionRank.Native

@[expose] def j3Prog : List Op :=
  [.pow 2 1 4, .pow 1 4 3, .mul 3 0 3, .mul 3 4 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 1 3,
   .mul 3 0 3, .mul 3 4 3, .mul 3 0 3, .mul 3 4 3, .mul 3 0 3, .mul 3 4 3, .mul 3 0 3, .mul 3 1 3,
   .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 4 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 1 3,
   .mul 3 0 3, .pow 1 4 5, .mul 5 0 5, .pow 14 3 6, .mul 5 6 5, .mul 5 1 5, .mul 5 6 5,
   .mul 5 0 5, .mul 5 4 5, .mul 5 0 5, .mul 5 3 5, .mul 5 1 5, .mul 5 0 5, .mul 5 1 5, .mul 5 0 5,
   .mul 5 1 5, .mul 5 6 5, .mul 5 4 5, .mul 5 6 5, .mul 5 4 5, .mul 5 6 5, .mul 5 0 5, .pow 1 3 7,
   .pow 2 5 2, .mul 7 2 7, .mul 7 1 7, .mul 7 5 7, .mul 7 1 7, .mul 7 5 7, .mul 7 0 7, .mul 7 3 7,
   .mul 7 4 7, .mul 7 0 7, .mul 7 5 7, .mul 7 4 7, .pow 5 5 8, .mul 7 8 7, .mul 7 4 7, .mul 7 6 7,
   .mul 7 5 7, .mul 7 1 7, .mul 7 8 7, .mul 7 0 7, .mul 7 6 7, .mul 7 4 7, .mul 7 0 7, .mul 7 4 7,
   .pow 13 3 2, .mul 7 2 7, .pow 4 5 2, .mul 7 2 7, .pow 13 3 2, .mul 7 2 7, .mul 7 8 7,
   .pow 1 6 9, .mul 9 0 9, .pow 13 3 2, .mul 9 2 9, .mul 9 7 9, .mul 9 8 9, .mul 9 4 9,
   .mul 9 8 9, .mul 9 0 9, .mul 9 8 9, .mul 9 7 9, .mul 9 8 9, .mul 9 7 9, .mul 9 8 9, .mul 9 6 9,
   .pow 4 5 10, .mul 10 6 10, .mul 10 4 10, .mul 10 7 10, .mul 10 0 10, .mul 10 9 10,
   .mul 10 8 10, .mul 10 4 10, .mul 10 6 10, .mul 10 8 10, .mul 10 6 10, .mul 10 0 10,
   .mul 10 4 10, .mul 10 8 10, .mul 10 9 10, .pow 13 3 2, .mul 10 2 10, .pow 1 9 11, .mul 11 5 11,
   .mul 11 3 11, .mul 11 7 11, .mul 11 0 11, .mul 11 1 11, .mul 11 7 11, .mul 11 1 11,
   .mul 11 9 11, .pow 2 5 2, .mul 11 2 11, .pow 2 9 12, .mul 12 3 12, .mul 12 7 12, .pow 2 3 2,
   .mul 12 2 12, .mul 12 9 12, .mul 12 0 12, .mul 12 10 12, .mul 12 3 12, .mul 12 7 12,
   .mul 12 1 12, .mul 12 5 12, .pow 1 10 13, .mul 13 3 13, .mul 13 5 13, .mul 13 7 13,
   .mul 13 9 13, .mul 13 0 13, .mul 13 7 13, .mul 13 3 13, .mul 13 0 13, .pow 1 9 14, .pow 2 3 2,
   .mul 14 2 14, .mul 14 5 14, .mul 14 9 14, .mul 14 10 14, .mul 14 3 14, .mul 14 0 14,
   .mul 14 5 14, .mul 14 3 14, .mul 14 1 14, .mul 14 7 14, .mul 14 0 14, .mul 14 5 14,
   .pow 1 7 15, .mul 15 10 15, .mul 15 9 15, .pow 2 3 2, .mul 15 2 15, .mul 15 7 15, .mul 15 3 15,
   .mul 15 10 15, .mul 15 0 15, .mul 15 7 15, .mul 15 3 15, .mul 15 1 15, .mul 15 5 15,
   .pow 0 0 16, .pow 2 12 17, .pow 1 11 18, .mul 18 12 18, .pow 1 11 19, .pow 2 12 2,
   .mul 19 2 19, .pow 2 11 20, .pow 2 11 21, .mul 21 12 21, .pow 2 11 22, .pow 2 12 2,
   .mul 22 2 22, .pow 1 7 23, .mul 23 3 23, .pow 3 5 2, .mul 23 2 23, .mul 23 3 23, .mul 23 0 23,
   .mul 23 9 23, .mul 23 0 23, .mul 23 1 23, .mul 23 0 23, .mul 23 7 23, .pow 2 9 24,
   .mul 24 10 24, .pow 2 3 2, .mul 24 2 24, .mul 24 10 24, .mul 24 3 24, .mul 24 5 24,
   .mul 24 0 24, .mul 24 3 24, .mul 24 10 24, .pow 2 3 2, .mul 24 2 24]

@[expose] def j3Nregs : Nat := 25

@[expose] def j3Mod : NMod where
  basis := [13, 14, 15]
  indep := [([0, 0, 1], 0), ([0, 0, 2], 0), ([0, 1, 0], 0), ([0, 1, 1], 0), ([0, 1, 2], 0),
      ([0, 2, 0], 0), ([0, 2, 1], 0), ([0, 2, 2], 0), ([1, 0, 0], 0), ([1, 0, 1], 0),
      ([1, 0, 2], 0), ([1, 1, 0], 0), ([1, 1, 1], 0), ([1, 1, 2], 0), ([1, 2, 0], 0),
      ([1, 2, 1], 0), ([1, 2, 2], 0), ([2, 0, 0], 0), ([2, 0, 1], 0), ([2, 0, 2], 0),
      ([2, 1, 0], 0), ([2, 1, 1], 0), ([2, 1, 2], 0), ([2, 2, 0], 0), ([2, 2, 1], 0),
      ([2, 2, 2], 0)]
  acts :=
    [{ reg := 11, ord := 9, mat := [1, 0, 1, 0, 1, 1, 0, 0, 1] },
     { reg := 12, ord := 9, mat := [1, 0, 0, 0, 1, 1, 0, 0, 1] },
     { reg := 16, ord := 1, mat := [1, 0, 0, 0, 1, 0, 0, 0, 1] },
     { reg := 17, ord := 9, mat := [1, 0, 0, 0, 1, 2, 0, 0, 1] },
     { reg := 18, ord := 9, mat := [1, 0, 1, 0, 1, 2, 0, 0, 1] },
     { reg := 19, ord := 9, mat := [1, 0, 1, 0, 1, 0, 0, 0, 1] },
     { reg := 20, ord := 9, mat := [1, 0, 2, 0, 1, 2, 0, 0, 1] },
     { reg := 21, ord := 9, mat := [1, 0, 2, 0, 1, 0, 0, 0, 1] },
     { reg := 22, ord := 9, mat := [1, 0, 2, 0, 1, 1, 0, 0, 1] },
     { reg := 23, ord := 8, mat := [1, 2, 0, 1, 1, 1, 0, 0, 2] },
     { reg := 24, ord := 9, mat := [1, 0, 2, 0, 1, 0, 0, 0, 1] }]

@[expose] def j3Tops : List Pc :=
  [{ reg := 11, ord := 9, pw := [(13, 2), (14, 1)],
     cj := [(12, [(12, 1), (13, 1), (14, 2), (15, 1)]), (13, [(13, 1)]), (14, [(14, 1)]),
           (15, [(13, 1), (14, 1), (15, 1)])] },
   { reg := 12, ord := 9, pw := [(13, 1)],
     cj := [(13, [(13, 1)]), (14, [(14, 1)]), (15, [(14, 1), (15, 1)])] }]

@[expose] def j3Gs : List NGrp :=
  [{ idx := 2, w := [] }, { idx := 1, w := [(12, 1)] },
    { idx := 3, w := [(12, 2)] }, { idx := 0, w := [(11, 1)] },
    { idx := 4, w := [(11, 1), (12, 1)] }, { idx := 5, w := [(11, 1), (12, 2)] },
    { idx := 6, w := [(11, 2)] }, { idx := 7, w := [(11, 2), (12, 1)] },
    { idx := 8, w := [(11, 2), (12, 2)] }]

@[expose] def j3CfSp : List (Nat × Nat) :=
  [(2, 1), (5, 2), (38, 1), (71, 2), (95, 1)]

@[expose] def j3CfArr : Array Nat :=
  j3CfSp.foldl (fun arr x => arr.set! x.1 x.2) (Array.replicate 99 0)

@[expose] def j3Cf (r₀ j s : Nat) : Int := (j3CfArr.getD ((r₀ * 11 + j) * 3 + s) 0 : Nat)

@[expose] def j3CiSp : List (Nat × Nat) :=
  [(2, 1), (11, 2), (110, 1), (200, 2), (203, 2), (204, 1), (209, 1), (281, 2), (284, 2),
   (299, 2), (303, 1), (308, 1), (398, 1), (401, 1), (402, 2), (407, 2), (506, 1), (578, 1),
   (581, 2), (596, 1), (599, 1), (600, 1), (602, 1), (605, 1), (611, 2), (677, 1), (680, 1),
   (695, 2), (698, 2), (699, 1), (710, 1), (776, 2), (779, 1)]

@[expose] def j3CiArr : Array Nat :=
  j3CiSp.foldl (fun arr x => arr.set! x.1 x.2) (Array.replicate 891 0)

@[expose] def j3Ci (a₀ b₀ j r s : Nat) : Int :=
  (j3CiArr.getD ((((a₀ * 3 + b₀) * 11 + j) * 3 + r) * 3 + s) 0 : Nat)

@[expose] def j3CtSp : List (Nat × Nat) :=
  [(80, 2)]

@[expose] def j3CtArr : Array Nat :=
  j3CtSp.foldl (fun arr x => arr.set! x.1 x.2) (Array.replicate 81 0)

@[expose] def j3Ct (a₀ b₀ r s : Nat) : Int :=
  (j3CtArr.getD ((((a₀ * 3 + b₀) * 3) + r) * 3 + s) 0 : Nat)

end CFSG.AGLEmbedding.R3.AlphaJ3
