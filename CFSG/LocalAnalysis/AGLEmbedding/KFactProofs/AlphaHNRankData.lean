module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRankDefs

public section

namespace CFSG.AGLEmbedding.R3.AlphaHNRank

open CFSG.SectionRank.Native

@[expose] def hnrlProg : List Op :=
  [.pow 1 0 3, .pow 2 1 4, .mul 3 4 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 4 3, .mul 3 0 3,
   .mul 3 4 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 4 3, .mul 3 0 3, .mul 3 4 3, .mul 3 0 3,
   .mul 3 4 3, .mul 3 0 3, .mul 3 4 3, .mul 3 0 3, .mul 3 4 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3,
   .mul 3 1 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3,
   .mul 3 4 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 4 3, .mul 3 0 3, .mul 3 4 3, .mul 3 0 3,
   .mul 3 4 3, .mul 3 0 3, .mul 3 4 3, .mul 3 0 3, .mul 3 4 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3,
   .mul 3 1 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3,
   .mul 3 4 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 4 3, .mul 3 0 3,
   .mul 3 1 3, .mul 3 0 3, .pow 1 1 5, .mul 5 3 5, .mul 5 0 5, .mul 5 4 5, .mul 5 0 5, .mul 5 4 5,
   .mul 5 3 5, .mul 5 1 5, .mul 5 3 5, .mul 5 0 5, .mul 5 4 5, .mul 5 0 5, .mul 5 4 5, .mul 5 0 5,
   .mul 5 3 5, .mul 5 4 5, .mul 5 0 5, .mul 5 3 5, .mul 5 1 5, .mul 5 3 5, .mul 5 4 5, .mul 5 0 5,
   .mul 5 4 5, .mul 5 3 5, .mul 5 1 5, .mul 5 3 5, .mul 5 0 5, .mul 5 3 5, .mul 5 0 5, .mul 5 3 5,
   .mul 5 4 5, .mul 5 0 5, .mul 5 4 5, .pow 10 5 7, .pow 1 7 6, .mul 6 3 6, .mul 6 5 6,
   .mul 6 0 6, .mul 6 1 6, .mul 6 3 6, .mul 6 4 6, .mul 6 5 6, .mul 6 3 6, .mul 6 1 6, .mul 6 7 6,
   .mul 6 0 6, .mul 6 1 6, .mul 6 0 6, .mul 6 5 6, .mul 6 0 6, .mul 6 7 6, .mul 6 0 6, .mul 6 5 6,
   .mul 6 0 6, .mul 6 3 6, .mul 6 0 6, .mul 6 7 6, .mul 6 0 6, .mul 6 1 6, .mul 6 3 6, .mul 6 7 6,
   .mul 6 3 6, .mul 6 0 6, .mul 6 1 6, .mul 6 0 6, .mul 6 7 6, .mul 6 3 6, .mul 6 0 6, .mul 6 1 6,
   .mul 6 0 6, .mul 6 3 6, .pow 8 5 2, .mul 6 2 6, .mul 6 3 6, .mul 6 7 6, .mul 6 3 6, .pow 9 5 2,
   .mul 6 2 6, .mul 6 3 6, .pow 8 5 2, .mul 6 2 6, .pow 1 7 8, .mul 8 1 8, .mul 8 6 8, .mul 8 7 8,
   .mul 8 3 8, .pow 5 6 9, .mul 8 9 8, .mul 8 4 8, .mul 8 0 8, .mul 8 4 8, .mul 8 7 8, .mul 8 4 8,
   .mul 8 0 8, .mul 8 9 8, .mul 8 4 8, .mul 8 0 8, .mul 8 7 8, .pow 4 6 2, .mul 8 2 8, .mul 8 3 8,
   .pow 9 5 2, .mul 8 2 8, .mul 8 3 8, .mul 8 7 8, .mul 8 3 8, .pow 1 3 10, .pow 5 8 11,
   .mul 10 11 10, .mul 10 3 10, .mul 10 5 10, .mul 10 0 10, .mul 10 3 10, .mul 10 4 10,
   .mul 10 9 10, .mul 10 4 10, .mul 10 3 10, .pow 9 5 2, .mul 10 2 10, .mul 10 4 10, .pow 3 6 2,
   .mul 10 2 10, .mul 10 4 10, .mul 10 9 10, .mul 10 11 10, .mul 10 3 10, .mul 10 9 10,
   .pow 9 5 2, .mul 10 2 10, .pow 1 8 12, .mul 12 10 12, .mul 12 8 12, .mul 12 6 12,
   .mul 12 10 12, .mul 12 8 12, .mul 12 6 12, .mul 12 10 12, .mul 12 8 12, .mul 12 6 12,
   .mul 12 10 12, .mul 12 3 12, .mul 12 6 12, .mul 12 8 12, .mul 12 5 12, .mul 12 6 12,
   .mul 12 8 12, .mul 12 3 12, .mul 12 0 12, .mul 12 1 12, .mul 12 0 12, .mul 12 1 12, .pow 2 6 2,
   .mul 12 2 12, .mul 12 0 12, .mul 12 10 12, .mul 12 8 12, .pow 3 8 13, .pow 2 10 2,
   .mul 13 2 13, .mul 13 6 13, .mul 13 10 13, .mul 13 8 13, .pow 2 6 2, .mul 13 2 13,
   .mul 13 8 13, .mul 13 5 13, .mul 13 3 13, .mul 13 6 13, .mul 13 10 13, .mul 13 5 13,
   .mul 13 3 13, .pow 2 1 14, .mul 13 14 13, .mul 13 5 13, .mul 13 10 13, .mul 13 8 13,
   .mul 13 1 13, .mul 13 10 13, .mul 13 8 13, .pow 1 6 15, .pow 3 8 2, .mul 15 2 15, .mul 15 6 15,
   .mul 15 3 15, .pow 2 8 2, .mul 15 2 15, .mul 15 6 15, .mul 15 3 15, .mul 15 10 15,
   .mul 15 8 15, .mul 15 1 15, .mul 15 6 15, .mul 15 5 15, .mul 15 8 15, .mul 15 1 15,
   .mul 15 3 15, .pow 2 10 2, .mul 15 2 15, .pow 5 8 17, .pow 1 17 16, .pow 2 6 2, .mul 16 2 16,
   .mul 16 10 16, .mul 16 8 16, .mul 16 3 16, .mul 16 8 16, .pow 2 6 2, .mul 16 2 16,
   .mul 16 10 16, .mul 16 1 16, .mul 16 5 16, .mul 16 10 16, .mul 16 5 16, .mul 16 10 16,
   .mul 16 6 16, .mul 16 1 16, .mul 16 6 16, .pow 1 6 18, .pow 2 8 2, .mul 18 2 18, .mul 18 6 18,
   .mul 18 10 18, .mul 18 8 18, .mul 18 10 18, .mul 18 6 18, .mul 18 8 18, .pow 2 5 2,
   .mul 18 2 18, .mul 18 3 18, .mul 18 5 18, .mul 18 6 18, .mul 18 8 18, .mul 18 0 18,
   .mul 18 3 18, .mul 18 14 18, .mul 18 6 18, .mul 18 8 18, .mul 18 6 18, .mul 18 3 18,
   .mul 18 1 18, .pow 1 6 19, .mul 19 8 19, .mul 19 10 19, .mul 19 6 19, .mul 19 8 19,
   .pow 2 10 2, .mul 19 2 19, .mul 19 6 19, .mul 19 10 19, .pow 3 8 2, .mul 19 2 19, .mul 19 3 19,
   .mul 19 10 19, .mul 19 5 19, .mul 19 3 19, .mul 19 5 19, .mul 19 0 19, .mul 19 1 19,
   .mul 19 8 19, .mul 19 5 19, .mul 19 0 19, .mul 19 6 19, .mul 19 1 19, .mul 19 8 19,
   .pow 4 19 21, .pow 1 21 20, .pow 1 18 22, .pow 3 19 2, .mul 22 2 22, .pow 1 6 23,
   .mul 23 10 23, .mul 23 8 23, .mul 23 10 23, .mul 23 8 23, .pow 2 10 2, .mul 23 2 23,
   .mul 23 6 23, .mul 23 10 23, .mul 23 8 23, .mul 23 5 23, .mul 23 3 23, .mul 23 6 23,
   .mul 23 10 23, .mul 23 6 23, .mul 23 3 23, .mul 23 0 23, .pow 2 5 2, .mul 23 2 23,
   .mul 23 6 23, .mul 23 5 23, .mul 23 0 23, .mul 23 6 23, .mul 23 14 23, .pow 1 10 24,
   .mul 24 6 24, .pow 2 10 2, .mul 24 2 24, .mul 24 8 24, .mul 24 10 24, .mul 24 8 24,
   .mul 24 10 24, .mul 24 5 24, .mul 24 3 24, .mul 24 6 24, .pow 2 8 2, .mul 24 2 24,
   .mul 24 3 24, .mul 24 5 24, .mul 24 1 24, .mul 24 0 24, .mul 24 1 24, .mul 24 5 24,
   .mul 24 3 24, .mul 24 10 24, .mul 24 5 24, .mul 24 3 24, .mul 24 0 24, .pow 2 12 25,
   .pow 4 15 26, .mul 25 26 25, .pow 3 16 2, .mul 25 2 25, .pow 2 18 2, .mul 25 2 25, .pow 3 19 2,
   .mul 25 2 25, .pow 1 21 27, .pow 2 10 28, .mul 28 6 28, .mul 28 8 28, .pow 2 10 2,
   .mul 28 2 28, .pow 2 6 2, .mul 28 2 28, .mul 28 3 28, .mul 28 5 28, .mul 28 6 28,
   .mul 28 10 28, .pow 2 5 2, .mul 28 2 28, .mul 28 1 28, .mul 28 8 28, .mul 28 1 28,
   .mul 28 6 28, .mul 28 5 28, .mul 28 10 28, .mul 28 1 28, .mul 28 8 28, .pow 2 6 29, .pow 3 8 2,
   .mul 29 2 29, .mul 29 6 29, .mul 29 10 29, .mul 29 8 29, .mul 29 10 29, .pow 2 6 2,
   .mul 29 2 29, .mul 29 8 29, .mul 29 3 29, .mul 29 10 29, .mul 29 6 29, .mul 29 8 29,
   .mul 29 6 29, .mul 29 3 29, .mul 29 6 29, .mul 29 0 29, .mul 29 1 29, .mul 29 6 29,
   .mul 29 10 29, .mul 29 3 29, .mul 29 14 29, .mul 29 6 29, .mul 29 3 29, .pow 11 23 30,
   .pow 19 28 31, .pow 24 24 32, .pow 1 30 33, .mul 33 31 33, .mul 33 30 33, .mul 33 29 33,
   .mul 33 23 33, .mul 33 23 33, .mul 33 29 33, .mul 33 28 33, .mul 33 29 33, .mul 33 30 33,
   .mul 33 29 33, .mul 33 32 33, .mul 33 32 33, .mul 33 23 33, .mul 33 24 33, .mul 33 30 33,
   .mul 33 24 33, .mul 33 30 33, .mul 33 23 33, .mul 33 23 33, .mul 33 29 33, .mul 33 28 33,
   .mul 33 32 33, .mul 33 29 33, .mul 33 29 33, .mul 33 23 33, .mul 33 29 33, .mul 33 32 33,
   .mul 33 30 33, .mul 33 32 33, .mul 33 24 33, .mul 33 29 33, .mul 33 24 33, .mul 33 28 33,
   .mul 33 23 33, .mul 33 30 33, .mul 33 29 33, .mul 33 30 33, .mul 33 29 33, .mul 33 32 33,
   .mul 33 32 33, .mul 33 31 33, .mul 33 32 33, .mul 33 29 33, .mul 33 30 33, .mul 33 30 33,
   .pow 19 33 34, .pow 1 28 35, .mul 35 30 35, .mul 35 33 35, .mul 35 23 35, .mul 35 31 35,
   .mul 35 33 35, .mul 35 31 35, .mul 35 31 35, .mul 35 33 35, .mul 35 30 35, .mul 35 34 35,
   .mul 35 29 35, .mul 35 31 35, .mul 35 29 35, .mul 35 31 35, .mul 35 31 35, .mul 35 30 35,
   .mul 35 34 35, .mul 35 29 35, .pow 5 35 36, .pow 1 32 37, .mul 37 28 37, .mul 37 35 37,
   .mul 37 35 37, .mul 37 36 37, .mul 37 34 37, .mul 37 29 37, .mul 37 23 37, .mul 37 23 37,
   .mul 37 33 37, .mul 37 36 37, .mul 37 32 37, .mul 37 30 37, .mul 37 36 37, .mul 37 30 37,
   .mul 37 34 37, .mul 37 31 37, .mul 37 32 37, .mul 37 30 37, .mul 37 36 37, .mul 37 36 37,
   .mul 37 34 37, .mul 37 36 37, .mul 37 34 37, .mul 37 34 37, .mul 37 34 37, .mul 37 36 37,
   .mul 37 34 37, .pow 4 37 38, .pow 1 37 39, .mul 39 28 39, .mul 39 29 39, .mul 39 30 39,
   .mul 39 29 39, .mul 39 38 39, .mul 39 28 39, .mul 39 28 39, .mul 39 36 39, .mul 39 29 39,
   .mul 39 36 39, .mul 39 36 39, .mul 39 36 39, .mul 39 34 39, .mul 39 34 39, .mul 39 30 39,
   .mul 39 31 39, .mul 39 36 39, .mul 39 36 39, .mul 39 36 39, .mul 39 36 39, .mul 39 34 39,
   .mul 39 38 39, .mul 39 38 39, .mul 39 34 39, .mul 39 36 39, .pow 1 34 40, .mul 40 29 40,
   .mul 40 28 40, .mul 40 24 40, .mul 40 29 40, .mul 40 35 40, .mul 40 31 40, .mul 40 23 40,
   .mul 40 29 40, .mul 40 29 40, .mul 40 32 40, .mul 40 34 40, .mul 40 29 40, .mul 40 38 40,
   .mul 40 30 40, .mul 40 30 40, .mul 40 39 40, .mul 40 32 40, .mul 40 39 40, .mul 40 38 40,
   .mul 40 38 40, .mul 40 38 40, .mul 40 39 40, .mul 40 34 40, .mul 40 36 40, .mul 40 34 40]

@[expose] def hnrlNregs : Nat := 41

@[expose] def hnrlPc : List Pc :=
  [{ reg := 12, ord := 5, pw := [], cj := [(13, [(13, 1), (15, 4), (16, 2), (18, 3), (19, 4)]),
     (15, [(15, 1)]), (16, [(16, 1), (19, 3)]), (18, [(18, 1), (19, 4)]), (19, [(19, 1)])] },
   { reg := 13, ord := 5, pw := [], cj := [(15, [(15, 1), (16, 4)]), (16, [(16, 1), (18, 4)]),
     (18, [(18, 1)]), (19, [(19, 1)])] },
   { reg := 15, ord := 5, pw := [], cj := [(16, [(16, 1), (19, 4)]), (18, [(18, 1)]), (19,
     [(19, 1)])] },
   { reg := 16, ord := 5, pw := [], cj := [(18, [(18, 1)]), (19, [(19, 1)])] },
   { reg := 18, ord := 5, pw := [], cj := [(19, [(19, 1)])] },
   { reg := 19, ord := 5, pw := [], cj := [] }]

@[expose] def hnrlMods : List RMod :=
  [{ nm :=
     { basis := [20, 22]
       indep := [([0, 1], 0), ([0, 2], 0), ([0, 3], 0), ([0, 4], 0), ([1, 0], 0), ([1, 1], 0),
           ([1, 2], 0), ([1, 3], 0), ([1, 4], 0), ([2, 0], 0), ([2, 1], 0), ([2, 2], 0),
           ([2, 3], 0), ([2, 4], 0), ([3, 0], 0), ([3, 1], 0), ([3, 2], 0), ([3, 3], 0),
           ([3, 4], 0), ([4, 0], 0), ([4, 1], 0), ([4, 2], 0), ([4, 3], 0), ([4, 4], 0)]
       acts :=
         [{ reg := 23, ord := 12, mat := [2, 3, 2, 0] },
          { reg := 24, ord := 25, mat := [3, 2, 3, 4] }] },
     ws := [[(19, 4)], [(18, 1), (19, 3)]] },
   { nm :=
     { basis := [25, 27]
       indep := [([0, 1], 0), ([0, 2], 0), ([0, 3], 0), ([0, 4], 0), ([1, 0], 0), ([1, 1], 0),
           ([1, 2], 0), ([1, 3], 0), ([1, 4], 0), ([2, 0], 0), ([2, 1], 0), ([2, 2], 0),
           ([2, 3], 0), ([2, 4], 0), ([3, 0], 0), ([3, 1], 0), ([3, 2], 0), ([3, 3], 0),
           ([3, 4], 0), ([4, 0], 0), ([4, 1], 0), ([4, 2], 0), ([4, 3], 0), ([4, 4], 0)]
       acts :=
         [{ reg := 28, ord := 20, mat := [4, 0, 3, 3] },
          { reg := 29, ord := 2, mat := [4, 0, 0, 1] }] },
     ws := [[(12, 2), (15, 4), (16, 3), (18, 2), (19, 3)], [(19, 4)]] }]

@[expose] def hnrlDers : List Der :=
  [{ reg := 30, ord := 12, w := [(23, 11)] },
   { reg := 31, ord := 20, w := [(28, 19)] },
   { reg := 32, ord := 25, w := [(24, 24)] },
   { reg := 33, ord := 20, w := [(30, 1), (31, 1), (30, 1), (29, 1), (23, 1), (23, 1), (29, 1),
     (28, 1), (29, 1), (30, 1), (29, 1), (32, 1), (32, 1), (23, 1), (24, 1), (30, 1), (24,
     1), (30, 1), (23, 1), (23, 1), (29, 1), (28, 1), (32, 1), (29, 1), (29, 1), (23, 1),
     (29, 1), (32, 1), (30, 1), (32, 1), (24, 1), (29, 1), (24, 1), (28, 1), (23, 1), (30,
     1), (29, 1), (30, 1), (29, 1), (32, 1), (32, 1), (31, 1), (32, 1), (29, 1), (30, 1),
     (30, 1)] },
   { reg := 34, ord := 20, w := [(33, 19)] },
   { reg := 35, ord := 6, w := [(28, 1), (30, 1), (33, 1), (23, 1), (31, 1), (33, 1), (31, 1),
     (31, 1), (33, 1), (30, 1), (34, 1), (29, 1), (31, 1), (29, 1), (31, 1), (31, 1), (30,
     1), (34, 1), (29, 1)] },
   { reg := 36, ord := 6, w := [(35, 5)] },
   { reg := 37, ord := 5, w := [(32, 1), (28, 1), (35, 1), (35, 1), (36, 1), (34, 1), (29, 1),
     (23, 1), (23, 1), (33, 1), (36, 1), (32, 1), (30, 1), (36, 1), (30, 1), (34, 1), (31,
     1), (32, 1), (30, 1), (36, 1), (36, 1), (34, 1), (36, 1), (34, 1), (34, 1), (34, 1),
     (36, 1), (34, 1)] },
   { reg := 38, ord := 5, w := [(37, 4)] },
   { reg := 39, ord := 2, w := [(37, 1), (28, 1), (29, 1), (30, 1), (29, 1), (38, 1), (28, 1),
     (28, 1), (36, 1), (29, 1), (36, 1), (36, 1), (36, 1), (34, 1), (34, 1), (30, 1), (31,
     1), (36, 1), (36, 1), (36, 1), (36, 1), (34, 1), (38, 1), (38, 1), (34, 1), (36, 1)] },
   { reg := 40, ord := 12, w := [(34, 1), (29, 1), (28, 1), (24, 1), (29, 1), (35, 1), (31, 1),
     (23, 1), (29, 1), (29, 1), (32, 1), (34, 1), (29, 1), (38, 1), (30, 1), (30, 1), (39,
     1), (32, 1), (39, 1), (38, 1), (38, 1), (38, 1), (39, 1), (34, 1), (36, 1), (34, 1)] }]

@[expose] def hnrlSpec : RSpec where
  p := 5
  pc := hnrlPc
  mods := hnrlMods
  ders := hnrlDers
  rA := 0
  oA := 2
  rB := 1
  oB := 3
  wA := [(39, 1), (37, 1), (40, 1), (37, 1), (40, 1), (37, 1), (37, 1), (40, 1), (33, 1), (33, 1),
      (39, 1), (35, 1), (35, 1), (37, 1), (37, 1), (28, 1), (23, 1), (39, 1), (33, 1), (39,
      1), (37, 1), (23, 1)]
  wB := [(40, 1), (37, 1), (40, 1), (37, 1), (39, 1), (37, 1), (40, 1), (37, 1), (40, 1), (40, 1),
      (40, 1), (35, 1), (39, 1), (33, 1), (37, 1), (39, 1), (33, 1), (23, 1), (24, 1), (28,
      1), (39, 1), (23, 1), (24, 1)]

@[expose] def hnrlCf1Sp : List (Nat × Nat) :=
  [(0, 3), (1, 1), (4, 4), (5, 2)]

@[expose] def hnrlCf1Arr : Array Nat :=
  hnrlCf1Sp.foldl (fun arr x => arr.set! x.1 x.2) (Array.replicate 8 0)

@[expose] def hnrlCf1 (r₀ j s : Nat) : Int := (hnrlCf1Arr.getD ((r₀ * 2 + j) * 2 + s) 0 : Nat)

@[expose] def hnrlCi1Sp : List (Nat × Nat) :=
  [(1, 3), (2, 3), (8, 2), (9, 2), (11, 3), (16, 2), (18, 2), (19, 3), (25, 2), (26, 2), (27, 4)]

@[expose] def hnrlCi1Arr : Array Nat :=
  hnrlCi1Sp.foldl (fun arr x => arr.set! x.1 x.2) (Array.replicate 32 0)

@[expose] def hnrlCi1 (a₀ b₀ j r s : Nat) : Int :=
  (hnrlCi1Arr.getD ((((a₀ * 2 + b₀) * 2 + j) * 2 + r) * 2 + s) 0 : Nat)

@[expose] def hnrlCt1Sp : List (Nat × Nat) := []

@[expose] def hnrlCt1Arr : Array Nat :=
  hnrlCt1Sp.foldl (fun arr x => arr.set! x.1 x.2) (Array.replicate 16 0)

@[expose] def hnrlCt1 (a₀ b₀ r s : Nat) : Int :=
  (hnrlCt1Arr.getD ((((a₀ * 2 + b₀) * 2) + r) * 2 + s) 0 : Nat)

@[expose] def hnrlCf2Sp : List (Nat × Nat) :=
  [(0, 2), (1, 2), (5, 3)]

@[expose] def hnrlCf2Arr : Array Nat :=
  hnrlCf2Sp.foldl (fun arr x => arr.set! x.1 x.2) (Array.replicate 8 0)

@[expose] def hnrlCf2 (r₀ j s : Nat) : Int := (hnrlCf2Arr.getD ((r₀ * 2 + j) * 2 + s) 0 : Nat)

@[expose] def hnrlCi2Sp : List (Nat × Nat) :=
  [(8, 2), (9, 2), (10, 1), (16, 2), (17, 1), (18, 2), (24, 2), (25, 1), (26, 1)]

@[expose] def hnrlCi2Arr : Array Nat :=
  hnrlCi2Sp.foldl (fun arr x => arr.set! x.1 x.2) (Array.replicate 32 0)

@[expose] def hnrlCi2 (a₀ b₀ j r s : Nat) : Int :=
  (hnrlCi2Arr.getD ((((a₀ * 2 + b₀) * 2 + j) * 2 + r) * 2 + s) 0 : Nat)

@[expose] def hnrlCt2Sp : List (Nat × Nat) :=
  [(0, 3)]

@[expose] def hnrlCt2Arr : Array Nat :=
  hnrlCt2Sp.foldl (fun arr x => arr.set! x.1 x.2) (Array.replicate 16 0)

@[expose] def hnrlCt2 (a₀ b₀ r s : Nat) : Int :=
  (hnrlCt2Arr.getD ((((a₀ * 2 + b₀) * 2) + r) * 2 + s) 0 : Nat)

@[expose] def hnrlTabs : List RLin :=
  [⟨hnrlCf1, hnrlCi1, hnrlCt1⟩, ⟨hnrlCf2, hnrlCi2, hnrlCt2⟩]

end CFSG.AGLEmbedding.R3.AlphaHNRank
