module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoverPointDefs

public section

namespace CFSG.AGLEmbedding.R3.O73Three

open CFSG.SectionRank.Native

@[expose] def seedA : String :=
  "1 3 7 7\n\
    2102112\n\
    0010121\n\
    0111022\n\
    1111222\n\
    0101000\n\
    0221000\n\
    2010110\n"

@[expose] def seedB : String :=
  "1 3 7 7\n\
    1020111\n\
    1112010\n\
    1022001\n\
    2201011\n\
    2220222\n\
    2001222\n\
    0121001\n"

@[expose] def nregs : Nat := 12

@[expose] def cpProg : List Op :=
  [.pow 1 0 3, .mul 3 1 3, .pow 2 0 2, .mul 3 2 3, .pow 2 1 2, .mul 3 2 3, .pow 2 0 2, .mul 3 2 3,
   .pow 2 1 2, .mul 3 2 3, .pow 2 0 2, .mul 3 2 3, .mul 3 1 3, .mul 3 0 3, .pow 2 1 2, .mul 3 2 3,
   .mul 3 0 3, .pow 2 1 2, .mul 3 2 3, .pow 2 0 2, .mul 3 2 3, .pow 2 1 2, .mul 3 2 3, .mul 3 0 3,
   .mul 3 1 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .pow 2 1 2, .mul 3 2 3, .mul 3 0 3, .pow 2 1 2,
   .mul 3 2 3, .mul 3 0 3, .mul 3 1 3, .pow 2 0 2, .mul 3 2 3, .pow 2 1 2, .mul 3 2 3, .mul 3 0 3,
   .mul 3 1 3, .mul 3 0 3, .mul 3 1 3, .pow 2 0 2, .mul 3 2 3, .mul 3 1 3, .mul 3 0 3, .pow 2 1 2,
   .mul 3 2 3, .pow 2 0 2, .mul 3 2 3, .mul 3 1 3, .pow 2 0 2, .mul 3 2 3, .mul 3 1 3, .pow 2 0 2,
   .mul 3 2 3, .pow 2 1 2, .mul 3 2 3, .mul 3 0 3, .pow 2 1 2, .mul 3 2 3, .pow 1 0 4, .mul 4 1 4,
   .mul 4 0 4, .mul 4 1 4, .pow 2 0 2, .mul 4 2 4, .pow 2 1 2, .mul 4 2 4, .mul 4 0 4, .mul 4 1 4,
   .pow 2 0 2, .mul 4 2 4, .pow 2 1 2, .mul 4 2 4, .mul 4 0 4, .pow 2 1 2, .mul 4 2 4, .pow 2 0 2,
   .mul 4 2 4, .mul 4 1 4, .mul 4 0 4, .mul 4 1 4, .pow 2 0 2, .mul 4 2 4, .pow 2 1 2, .mul 4 2 4,
   .mul 4 0 4, .mul 4 1 4, .pow 2 0 2, .mul 4 2 4, .pow 2 1 2, .mul 4 2 4, .mul 4 0 4, .mul 4 1 4,
   .pow 2 0 2, .mul 4 2 4, .pow 2 1 2, .mul 4 2 4, .pow 2 0 2, .mul 4 2 4, .pow 2 1 2, .mul 4 2 4,
   .pow 2 0 2, .mul 4 2 4, .pow 2 1 2, .mul 4 2 4, .mul 4 0 4, .pow 2 1 2, .mul 4 2 4, .pow 2 0 2,
   .mul 4 2 4, .mul 4 1 4, .mul 4 0 4, .mul 4 1 4, .pow 2 0 2, .mul 4 2 4, .mul 4 1 4, .pow 2 0 2,
   .mul 4 2 4, .pow 2 1 2, .mul 4 2 4, .mul 4 0 4, .mul 4 1 4, .mul 4 0 4, .mul 4 1 4, .mul 4 0 4,
   .pow 2 1 2, .mul 4 2 4, .mul 4 0 4, .mul 4 1 4, .mul 4 0 4, .pow 2 1 2, .mul 4 2 4, .pow 2 0 2,
   .mul 4 2 4, .mul 4 1 4, .mul 4 0 4, .pow 2 1 2, .mul 4 2 4, .pow 2 0 2, .mul 4 2 4, .pow 2 1 2,
   .mul 4 2 4, .pow 2 0 2, .mul 4 2 4, .pow 2 1 2, .mul 4 2 4, .pow 2 0 2, .mul 4 2 4, .pow 2 1 2,
   .mul 4 2 4, .pow 2 0 2, .mul 4 2 4, .mul 4 1 4, .pow 2 0 2, .mul 4 2 4, .pow 2 1 2, .mul 4 2 4,
   .pow 2 0 2, .mul 4 2 4, .pow 2 1 2, .mul 4 2 4, .pow 2 0 2, .mul 4 2 4, .pow 1 0 5, .pow 2 1 2,
   .mul 5 2 5, .mul 5 0 5, .pow 2 1 2, .mul 5 2 5, .mul 5 0 5, .pow 2 1 2, .mul 5 2 5, .pow 2 0 2,
   .mul 5 2 5, .mul 5 1 5, .mul 5 0 5, .mul 5 1 5, .mul 5 0 5, .mul 5 1 5, .mul 5 0 5, .mul 5 1 5,
   .pow 2 0 2, .mul 5 2 5, .mul 5 1 5, .mul 5 0 5, .pow 2 1 2, .mul 5 2 5, .pow 2 0 2, .mul 5 2 5,
   .mul 5 1 5, .pow 2 0 2, .mul 5 2 5, .mul 5 1 5, .pow 2 0 2, .mul 5 2 5, .mul 5 1 5, .pow 2 0 2,
   .mul 5 2 5, .pow 2 1 2, .mul 5 2 5, .mul 5 0 5, .mul 5 1 5, .pow 2 0 2, .mul 5 2 5, .mul 5 1 5,
   .mul 5 0 5, .pow 2 1 2, .mul 5 2 5, .mul 5 0 5, .pow 2 1 2, .mul 5 2 5, .mul 5 0 5, .mul 5 1 5,
   .mul 5 0 5, .mul 5 1 5, .pow 2 0 2, .mul 5 2 5, .pow 2 1 2, .mul 5 2 5, .mul 5 0 5, .pow 2 1 2,
   .mul 5 2 5, .pow 2 0 2, .mul 5 2 5, .pow 2 1 2, .mul 5 2 5, .mul 5 0 5, .pow 2 1 2, .mul 5 2 5,
   .mul 5 0 5, .pow 2 1 2, .mul 5 2 5, .pow 2 0 2, .mul 5 2 5, .pow 2 1 6, .pow 2 0 2, .mul 6 2 6,
   .pow 2 1 2, .mul 6 2 6, .mul 6 0 6, .pow 2 1 2, .mul 6 2 6, .pow 2 0 2, .mul 6 2 6, .mul 6 1 6,
   .mul 6 0 6, .mul 6 1 6, .pow 2 0 2, .mul 6 2 6, .pow 2 1 2, .mul 6 2 6, .mul 6 0 6, .pow 2 1 2,
   .mul 6 2 6, .mul 6 0 6, .pow 2 1 2, .mul 6 2 6, .pow 2 0 2, .mul 6 2 6, .mul 6 1 6, .mul 6 0 6,
   .mul 6 1 6, .pow 2 0 2, .mul 6 2 6, .mul 6 1 6, .mul 6 0 6, .pow 2 1 2, .mul 6 2 6, .pow 2 0 2,
   .mul 6 2 6, .pow 2 1 2, .mul 6 2 6, .pow 2 0 2, .mul 6 2 6, .pow 2 1 2, .mul 6 2 6, .pow 2 0 2,
   .mul 6 2 6, .pow 2 1 2, .mul 6 2 6, .mul 6 0 6, .mul 6 1 6, .pow 2 0 2, .mul 6 2 6, .mul 6 1 6,
   .mul 6 0 6, .mul 6 1 6, .mul 6 0 6, .pow 2 1 2, .mul 6 2 6, .mul 6 0 6, .mul 6 1 6, .mul 6 0 6,
   .mul 6 1 6, .mul 6 0 6, .mul 6 1 6, .mul 6 0 6, .mul 6 1 6, .pow 2 0 2, .mul 6 2 6, .pow 2 1 2,
   .mul 6 2 6, .pow 2 0 2, .mul 6 2 6, .pow 2 1 2, .mul 6 2 6, .pow 2 0 2, .mul 6 2 6, .mul 6 1 6,
   .mul 6 0 6, .pow 2 1 2, .mul 6 2 6, .mul 6 0 6, .pow 2 1 2, .mul 6 2 6, .pow 2 0 2, .mul 6 2 6,
   .pow 2 1 2, .mul 6 2 6, .mul 6 0 6, .mul 6 1 6, .pow 2 0 2, .mul 6 2 6, .mul 6 1 6, .pow 2 0 2,
   .mul 6 2 6, .mul 6 1 6, .pow 2 0 2, .mul 6 2 6, .pow 1 1 7, .pow 2 0 2, .mul 7 2 7, .mul 7 1 7,
   .pow 2 0 2, .mul 7 2 7, .mul 7 1 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .pow 2 1 2, .mul 7 2 7,
   .pow 2 0 2, .mul 7 2 7, .mul 7 1 7, .pow 2 0 2, .mul 7 2 7, .mul 7 1 7, .pow 2 0 2, .mul 7 2 7,
   .pow 2 1 2, .mul 7 2 7, .pow 2 0 2, .mul 7 2 7, .pow 2 1 2, .mul 7 2 7, .mul 7 0 7, .pow 2 1 2,
   .mul 7 2 7, .mul 7 0 7, .pow 2 1 2, .mul 7 2 7, .mul 7 0 7, .pow 2 1 2, .mul 7 2 7, .mul 7 0 7,
   .pow 2 1 2, .mul 7 2 7, .pow 2 0 2, .mul 7 2 7, .mul 7 1 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7,
   .mul 7 1 7, .mul 7 0 7, .mul 7 1 7, .pow 2 0 2, .mul 7 2 7, .pow 2 1 2, .mul 7 2 7, .mul 7 0 7,
   .mul 7 1 7, .pow 2 0 2, .mul 7 2 7, .pow 2 1 2, .mul 7 2 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7,
   .mul 7 1 7, .mul 7 0 7, .pow 2 1 2, .mul 7 2 7, .pow 2 0 2, .mul 7 2 7, .pow 2 1 2, .mul 7 2 7,
   .pow 2 0 2, .mul 7 2 7, .mul 7 1 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .mul 7 1 7, .pow 2 0 2,
   .mul 7 2 7, .mul 7 1 7, .pow 2 0 2, .mul 7 2 7, .pow 2 1 2, .mul 7 2 7, .pow 2 0 2, .mul 7 2 7,
   .pow 2 1 2, .mul 7 2 7, .pow 1 0 8, .mul 8 1 8, .pow 2 0 2, .mul 8 2 8, .mul 8 1 8, .mul 8 0 8,
   .mul 8 1 8, .pow 2 0 2, .mul 8 2 8, .pow 2 1 2, .mul 8 2 8, .pow 2 0 2, .mul 8 2 8, .pow 2 1 2,
   .mul 8 2 8, .mul 8 0 8, .pow 2 1 2, .mul 8 2 8, .pow 2 0 2, .mul 8 2 8, .mul 8 1 8, .mul 8 0 8,
   .mul 8 1 8, .mul 8 0 8, .pow 2 1 2, .mul 8 2 8, .mul 8 0 8, .pow 2 1 2, .mul 8 2 8, .mul 8 0 8,
   .pow 2 1 2, .mul 8 2 8, .mul 8 0 8, .mul 8 1 8, .pow 2 0 2, .mul 8 2 8, .pow 2 1 2, .mul 8 2 8,
   .mul 8 0 8, .mul 8 1 8, .mul 8 0 8, .pow 2 1 2, .mul 8 2 8, .pow 2 0 2, .mul 8 2 8, .pow 2 1 2,
   .mul 8 2 8, .pow 2 0 2, .mul 8 2 8, .pow 2 1 2, .mul 8 2 8, .pow 2 0 2, .mul 8 2 8, .pow 2 1 2,
   .mul 8 2 8, .pow 2 0 2, .mul 8 2 8, .pow 2 1 2, .mul 8 2 8, .pow 2 0 2, .mul 8 2 8, .pow 2 1 2,
   .mul 8 2 8, .pow 2 0 2, .mul 8 2 8, .pow 2 1 2, .mul 8 2 8, .mul 8 0 8, .mul 8 1 8, .pow 2 0 2,
   .mul 8 2 8, .mul 8 1 8, .pow 2 0 2, .mul 8 2 8, .mul 8 1 8, .pow 2 0 2, .mul 8 2 8, .mul 8 1 8,
   .mul 8 0 8, .mul 8 1 8, .mul 8 0 8, .mul 8 1 8, .mul 8 0 8, .mul 8 1 8, .pow 2 0 2, .mul 8 2 8,
   .pow 2 1 2, .mul 8 2 8, .mul 8 0 8, .pow 2 1 2, .mul 8 2 8, .mul 8 0 8, .pow 2 1 2, .mul 8 2 8,
   .mul 8 0 8, .pow 2 1 2, .mul 8 2 8, .pow 1 1 9, .pow 2 0 2, .mul 9 2 9, .mul 9 1 9, .pow 2 0 2,
   .mul 9 2 9, .mul 9 1 9, .pow 2 0 2, .mul 9 2 9, .mul 9 1 9, .mul 9 0 9, .pow 2 1 2, .mul 9 2 9,
   .pow 2 0 2, .mul 9 2 9, .pow 2 1 2, .mul 9 2 9, .pow 2 0 2, .mul 9 2 9, .pow 2 1 2, .mul 9 2 9,
   .pow 2 0 2, .mul 9 2 9, .pow 2 1 2, .mul 9 2 9, .mul 9 0 9, .pow 2 1 2, .mul 9 2 9, .mul 9 0 9,
   .pow 2 1 2, .mul 9 2 9, .mul 9 0 9, .pow 2 1 2, .mul 9 2 9, .pow 2 0 2, .mul 9 2 9, .mul 9 1 9,
   .mul 9 0 9, .mul 9 1 9, .mul 9 0 9, .pow 2 1 2, .mul 9 2 9, .mul 9 0 9, .pow 2 1 2, .mul 9 2 9,
   .mul 9 0 9, .pow 2 1 2, .mul 9 2 9, .mul 9 0 9, .mul 9 1 9, .pow 2 0 2, .mul 9 2 9, .pow 2 1 2,
   .mul 9 2 9, .mul 9 0 9, .mul 9 1 9, .pow 2 0 2, .mul 9 2 9, .mul 9 1 9, .pow 2 0 2, .mul 9 2 9,
   .mul 9 1 9, .pow 2 0 2, .mul 9 2 9, .mul 9 1 9, .mul 9 0 9, .mul 9 1 9, .mul 9 0 9, .mul 9 1 9,
   .pow 2 0 2, .mul 9 2 9, .pow 2 1 2, .mul 9 2 9, .mul 9 0 9, .mul 9 1 9, .pow 2 0 2, .mul 9 2 9,
   .pow 2 1 2, .mul 9 2 9, .mul 9 0 9, .pow 2 1 2, .mul 9 2 9, .mul 9 0 9, .pow 2 1 2, .mul 9 2 9,
   .pow 2 0 2, .mul 9 2 9, .pow 2 1 2, .mul 9 2 9, .pow 2 0 2, .mul 9 2 9, .mul 9 1 9, .pow 2 0 2,
   .mul 9 2 9, .pow 2 1 2, .mul 9 2 9, .mul 9 0 9, .pow 2 1 2, .mul 9 2 9, .pow 2 0 2, .mul 9 2 9,
   .mul 9 1 9, .pow 2 0 2, .mul 9 2 9, .pow 1 1 10, .pow 2 0 2, .mul 10 2 10, .pow 2 1 2,
   .mul 10 2 10, .mul 10 0 10, .mul 10 1 10, .mul 10 0 10, .mul 10 1 10, .pow 2 0 2, .mul 10 2 10,
   .mul 10 1 10, .mul 10 0 10, .pow 2 1 2, .mul 10 2 10, .pow 2 0 2, .mul 10 2 10, .pow 2 1 2,
   .mul 10 2 10, .pow 2 0 2, .mul 10 2 10, .mul 10 1 10, .mul 10 0 10, .pow 2 1 2, .mul 10 2 10,
   .pow 2 0 2, .mul 10 2 10, .pow 2 1 2, .mul 10 2 10, .mul 10 0 10, .pow 2 1 2, .mul 10 2 10,
   .pow 2 0 2, .mul 10 2 10, .pow 2 1 2, .mul 10 2 10, .pow 2 0 2, .mul 10 2 10, .pow 2 1 2,
   .mul 10 2 10, .pow 2 0 2, .mul 10 2 10, .pow 2 1 2, .mul 10 2 10, .pow 2 0 2, .mul 10 2 10,
   .pow 2 1 2, .mul 10 2 10, .mul 10 0 10, .mul 10 1 10, .pow 2 0 2, .mul 10 2 10, .mul 10 1 10,
   .pow 2 0 2, .mul 10 2 10, .mul 10 1 10, .pow 2 0 2, .mul 10 2 10, .mul 10 1 10, .mul 10 0 10,
   .mul 10 1 10, .mul 10 0 10, .pow 2 1 2, .mul 10 2 10, .pow 2 0 2, .mul 10 2 10, .mul 10 1 10,
   .pow 2 0 2, .mul 10 2 10, .mul 10 1 10, .pow 2 0 2, .mul 10 2 10, .mul 10 1 10, .pow 2 0 2,
   .mul 10 2 10, .pow 2 1 2, .mul 10 2 10, .pow 2 0 2, .mul 10 2 10, .pow 2 1 2, .mul 10 2 10,
   .pow 2 0 2, .mul 10 2 10, .pow 2 1 2, .mul 10 2 10, .mul 10 0 10, .pow 2 1 2, .mul 10 2 10,
   .mul 10 0 10, .pow 2 1 2, .mul 10 2 10, .mul 10 0 10, .pow 2 1 2, .mul 10 2 10, .pow 2 0 2,
   .mul 10 2 10, .mul 10 1 10, .mul 10 0 10, .mul 10 1 10, .mul 10 0 10, .mul 10 1 10, .pow 2 0 2,
   .mul 10 2 10, .pow 2 1 2, .mul 10 2 10, .mul 10 0 10, .pow 2 1 2, .mul 10 2 10, .mul 10 0 10,
   .pow 2 1 2, .mul 10 2 10, .mul 10 0 10, .pow 2 1 2, .mul 10 2 10, .pow 1 5 11]

@[expose] def cpSpec : CpSpec where
  p := 3
  m :=
    { b0 := 3, b1 := 4, b2 := 5, w0 := [(3, 1)], w1 := [(4, 1)], w2 := [(5, 1)],
      indep := [(0, 0, 1, 3), (0, 0, 2, 3), (0, 1, 0, 3), (0, 1, 1, 3), (0, 1, 2, 3), (0, 2, 0, 3),
        (0, 2, 1, 3), (0, 2, 2, 3), (1, 0, 0, 3), (1, 0, 1, 3), (1, 0, 2, 3), (1, 1, 0, 4),
        (1, 1, 1, 3), (1, 1, 2, 3), (1, 2, 0, 3), (1, 2, 1, 3), (1, 2, 2, 3), (2, 0, 0, 3),
        (2, 0, 1, 3), (2, 0, 2, 3), (2, 1, 0, 3), (2, 1, 1, 3), (2, 1, 2, 3), (2, 2, 0, 4),
        (2, 2, 1, 3), (2, 2, 2, 3)],
      acts := [{ reg := 6, ord := 6, mat := [0, 1, 2, 1, 0, 0, 0, 0, 2] },
        { reg := 7, ord := 13, mat := [0, 2, 2, 0, 1, 2, 2, 1, 1] }] }
  pts :=
    [{ reg := 11, w := [(3, 0), (4, 0), (5, 1)], t := 3,
       hs := [{ reg := 8, ord := 3, e := 1 }, { reg := 9, ord := 3, e := 1 },
         { reg := 10, ord := 6, e := 2 }] }]
  rA := 0
  oA := 3
  rB := 1
  oB := 3
  wA := [(9, 2), (6, 1), (10, 5), (9, 1), (10, 1), (6, 5), (9, 2), (10, 4), (6, 4), (7, 1), (10, 5),
    (7, 12), (8, 2), (7, 12), (6, 1), (9, 1), (10, 1), (6, 4), (8, 1), (7, 1)]
  wB := [(10, 4), (9, 1), (6, 1), (9, 1), (10, 5), (9, 2), (6, 1), (10, 1), (6, 2), (10, 1), (6, 1),
    (10, 5), (6, 5), (10, 4), (8, 2), (10, 4), (7, 12)]

end CFSG.AGLEmbedding.R3.O73Three
