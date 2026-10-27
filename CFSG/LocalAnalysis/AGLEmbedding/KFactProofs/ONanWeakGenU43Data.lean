module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoverPointDefs

public section

namespace CFSG.AGLEmbedding.R3.U43Three

open CFSG.SectionRank.Native

@[expose] def seedA : String :=
  "1 3 8 8\n\
    01011100\n\
    20202100\n\
    01001120\n\
    20002102\n\
    21210122\n\
    22222012\n\
    00101201\n\
    00011120\n"

@[expose] def seedB : String :=
  "1 3 8 8\n\
    20122222\n\
    02111212\n\
    02201100\n\
    10022100\n\
    00121001\n\
    00110120\n\
    21121110\n\
    22112101\n"

@[expose] def nregs : Nat := 16

@[expose] def cpProg : List Op :=
  [.pow 3 0 2, .pow 11 1 3, .pow 1 3 4, .mul 4 2 4, .mul 4 3 4, .mul 4 0 4, .mul 4 1 4, .mul 4 0 4,
   .mul 4 3 4, .mul 4 0 4, .mul 4 3 4, .mul 4 0 4, .mul 4 1 4, .mul 4 0 4, .mul 4 1 4, .mul 4 1 4,
   .mul 4 2 4, .mul 4 3 4, .mul 4 2 4, .mul 4 1 4, .mul 4 2 4, .mul 4 3 4, .mul 4 2 4, .mul 4 3 4,
   .mul 4 2 4, .mul 4 3 4, .mul 4 0 4, .mul 4 3 4, .mul 4 3 4, .mul 4 2 4, .mul 4 3 4, .mul 4 0 4,
   .mul 4 0 4, .mul 4 1 4, .mul 4 1 4, .pow 1 0 5, .mul 5 3 5, .mul 5 0 5, .mul 5 3 5, .mul 5 0 5,
   .mul 5 1 5, .mul 5 1 5, .mul 5 0 5, .mul 5 1 5, .mul 5 0 5, .mul 5 1 5, .mul 5 1 5, .mul 5 0 5,
   .mul 5 1 5, .mul 5 1 5, .mul 5 2 5, .mul 5 3 5, .mul 5 3 5, .mul 5 3 5, .mul 5 2 5, .mul 5 1 5,
   .mul 5 1 5, .mul 5 2 5, .mul 5 1 5, .mul 5 0 5, .mul 5 1 5, .mul 5 0 5, .mul 5 1 5, .mul 5 0 5,
   .mul 5 1 5, .mul 5 0 5, .mul 5 0 5, .mul 5 1 5, .mul 5 1 5, .pow 1 0 6, .mul 6 1 6, .mul 6 0 6,
   .mul 6 1 6, .mul 6 0 6, .mul 6 3 6, .mul 6 0 6, .mul 6 1 6, .mul 6 0 6, .mul 6 1 6, .mul 6 2 6,
   .mul 6 3 6, .mul 6 2 6, .mul 6 3 6, .mul 6 2 6, .mul 6 3 6, .mul 6 2 6, .mul 6 3 6, .mul 6 2 6,
   .mul 6 3 6, .mul 6 3 6, .mul 6 2 6, .mul 6 3 6, .mul 6 0 6, .mul 6 1 6, .mul 6 1 6, .mul 6 2 6,
   .mul 6 3 6, .pow 1 3 7, .mul 7 3 7, .mul 7 2 7, .mul 7 2 7, .mul 7 1 7, .mul 7 0 7, .mul 7 1 7,
   .mul 7 1 7, .mul 7 0 7, .mul 7 3 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .mul 7 3 7, .mul 7 0 7,
   .mul 7 3 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .mul 7 3 7, .mul 7 3 7, .mul 7 2 7, .mul 7 1 7,
   .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .mul 7 3 7, .mul 7 2 7, .mul 7 3 7,
   .mul 7 3 7, .mul 7 0 7, .mul 7 1 7, .mul 7 2 7, .mul 7 3 7, .mul 7 3 7, .mul 7 2 7, .mul 7 1 7,
   .mul 7 0 7, .mul 7 1 7, .mul 7 1 7, .mul 7 1 7, .mul 7 0 7, .mul 7 3 7, .mul 7 0 7, .mul 7 3 7,
   .mul 7 2 7, .mul 7 3 7, .pow 1 3 8, .mul 8 2 8, .mul 8 3 8, .mul 8 2 8, .mul 8 3 8, .mul 8 2 8,
   .mul 8 3 8, .mul 8 0 8, .mul 8 3 8, .mul 8 3 8, .mul 8 0 8, .mul 8 1 8, .mul 8 1 8, .mul 8 1 8,
   .mul 8 0 8, .mul 8 1 8, .mul 8 1 8, .mul 8 2 8, .mul 8 3 8, .mul 8 2 8, .mul 8 3 8, .mul 8 3 8,
   .mul 8 3 8, .mul 8 2 8, .mul 8 1 8, .mul 8 2 8, .mul 8 3 8, .mul 8 3 8, .mul 8 2 8, .mul 8 3 8,
   .mul 8 2 8, .mul 8 3 8, .mul 8 2 8, .pow 1 1 9, .mul 9 1 9, .mul 9 0 9, .mul 9 1 9, .mul 9 2 9,
   .mul 9 3 9, .mul 9 3 9, .mul 9 2 9, .mul 9 3 9, .mul 9 3 9, .mul 9 0 9, .mul 9 3 9, .mul 9 0 9,
   .mul 9 1 9, .mul 9 0 9, .mul 9 3 9, .mul 9 3 9, .mul 9 2 9, .mul 9 1 9, .mul 9 0 9, .mul 9 1 9,
   .mul 9 0 9, .mul 9 1 9, .mul 9 0 9, .mul 9 3 9, .mul 9 0 9, .mul 9 3 9, .mul 9 0 9, .mul 9 3 9,
   .mul 9 3 9, .mul 9 2 9, .mul 9 3 9, .pow 1 4 10, .pow 2 5 11, .mul 10 11 10, .pow 2 6 12,
   .mul 10 12 10, .pow 1 1 13, .mul 13 0 13, .mul 13 1 13, .mul 13 1 13, .mul 13 2 13,
   .mul 13 3 13, .mul 13 2 13, .mul 13 3 13, .mul 13 2 13, .mul 13 3 13, .mul 13 2 13,
   .mul 13 1 13, .mul 13 2 13, .mul 13 3 13, .mul 13 2 13, .mul 13 3 13, .mul 13 2 13,
   .mul 13 1 13, .mul 13 2 13, .mul 13 1 13, .mul 13 2 13, .mul 13 1 13, .mul 13 2 13,
   .mul 13 3 13, .mul 13 2 13, .mul 13 1 13, .mul 13 2 13, .mul 13 3 13, .mul 13 0 13,
   .mul 13 3 13, .mul 13 3 13, .mul 13 2 13, .mul 13 3 13, .pow 1 3 14, .mul 14 3 14, .mul 14 2 14,
   .mul 14 2 14, .mul 14 1 14, .mul 14 0 14, .mul 14 1 14, .mul 14 1 14, .mul 14 0 14,
   .mul 14 1 14, .mul 14 1 14, .mul 14 1 14, .mul 14 0 14, .mul 14 1 14, .mul 14 0 14,
   .mul 14 3 14, .mul 14 3 14, .mul 14 0 14, .mul 14 3 14, .mul 14 0 14, .mul 14 3 14,
   .mul 14 0 14, .mul 14 3 14, .mul 14 3 14, .mul 14 0 14, .mul 14 3 14, .mul 14 0 14,
   .mul 14 1 14, .mul 14 1 14, .mul 14 1 14, .mul 14 0 14, .mul 14 3 14, .mul 14 0 14,
   .mul 14 3 14, .mul 14 0 14, .mul 14 1 14, .mul 14 2 14, .pow 1 1 15, .mul 15 0 15, .mul 15 1 15,
   .mul 15 1 15, .mul 15 0 15, .mul 15 1 15, .mul 15 1 15, .mul 15 1 15, .mul 15 0 15,
   .mul 15 1 15, .mul 15 1 15, .mul 15 0 15, .mul 15 1 15, .mul 15 0 15, .mul 15 1 15,
   .mul 15 0 15, .mul 15 1 15, .mul 15 1 15, .mul 15 1 15, .mul 15 2 15, .mul 15 3 15,
   .mul 15 0 15, .mul 15 1 15, .mul 15 0 15, .mul 15 1 15, .mul 15 1 15, .mul 15 0 15,
   .mul 15 3 15, .mul 15 0 15, .mul 15 1 15, .mul 15 0 15, .mul 15 1 15, .mul 15 0 15,
   .mul 15 1 15, .mul 15 1 15, .mul 15 0 15, .mul 15 1 15, .mul 15 1 15]

@[expose] def cpSpec : CpSpec where
  p := 3
  m :=
    { b0 := 4, b1 := 5, b2 := 6, w0 := [(4, 1)], w1 := [(5, 1)], w2 := [(6, 1)],
      indep := [(0, 0, 1, 0), (0, 0, 2, 0), (0, 1, 0, 0), (0, 1, 1, 0), (0, 1, 2, 0), (0, 2, 0, 0),
        (0, 2, 1, 0), (0, 2, 2, 0), (1, 0, 0, 0), (1, 0, 1, 0), (1, 0, 2, 0), (1, 1, 0, 0),
        (1, 1, 1, 0), (1, 1, 2, 0), (1, 2, 0, 0), (1, 2, 1, 0), (1, 2, 2, 0), (2, 0, 0, 0),
        (2, 0, 1, 0), (2, 0, 2, 0), (2, 1, 0, 0), (2, 1, 1, 0), (2, 1, 2, 0), (2, 2, 0, 0),
        (2, 2, 1, 0), (2, 2, 2, 0)],
      acts := [{ reg := 7, ord := 2, mat := [1, 1, 0, 0, 2, 0, 0, 0, 2] },
        { reg := 8, ord := 3, mat := [1, 2, 1, 0, 1, 0, 0, 0, 1] },
        { reg := 9, ord := 8, mat := [2, 2, 1, 0, 0, 2, 0, 1, 0] }] }
  pts :=
    [{ reg := 10, w := [(4, 1), (5, 2), (6, 2)], t := 0,
       hs := [{ reg := 13, ord := 3, e := 1 }, { reg := 14, ord := 2, e := 2 },
         { reg := 15, ord := 12, e := 2 }] }]
  rA := 0
  oA := 4
  rB := 1
  oB := 12
  wA := [(7, 1), (9, 7), (7, 1), (13, 2), (9, 1), (7, 1), (9, 1), (15, 10), (14, 1), (9, 7),
    (15, 11), (9, 1), (15, 11), (8, 2), (14, 1), (15, 11)]
  wB := [(15, 1), (8, 2), (13, 1), (15, 11), (9, 7), (14, 1), (15, 10), (9, 1), (15, 1), (9, 7),
    (15, 10)]

end CFSG.AGLEmbedding.R3.U43Three
