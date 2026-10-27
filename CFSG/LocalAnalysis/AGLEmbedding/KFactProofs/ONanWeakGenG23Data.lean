module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoverPointDefs

public section

namespace CFSG.AGLEmbedding.R3.G23Three

open CFSG.SectionRank.Native

@[expose] def seedA : String :=
  "1 3 14 14\n\
    20000110100000\n\
    02000110100000\n\
    00112110100000\n\
    00020122021000\n\
    00002012221000\n\
    00000100000021\n\
    00000010000021\n\
    00000001021000\n\
    00000000100021\n\
    00000000020221\n\
    00000000002221\n\
    00000000000121\n\
    00000000000020\n\
    00000000000002\n"

@[expose] def seedB : String :=
  "1 3 14 14\n\
    10000000000000\n\
    10000100000000\n\
    10020200000000\n\
    10120100000000\n\
    00110100010000\n\
    12000200000000\n\
    02000110000000\n\
    00110122020000\n\
    02000120000010\n\
    02111212010000\n\
    02001111010220\n\
    02002102021210\n\
    02000120200020\n\
    00000000200011\n"

@[expose] def nregs : Nat := 11

@[expose] def cpProg : List Op :=
  [.pow 1 1 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .pow 2 1 2, .mul 3 2 3,
   .mul 3 0 3, .pow 2 1 2, .mul 3 2 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .pow 2 1 2, .mul 3 2 3,
   .mul 3 0 3, .pow 2 1 2, .mul 3 2 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .pow 2 1 2, .mul 3 2 3,
   .mul 3 0 3, .pow 2 1 2, .mul 3 2 3, .mul 3 0 3, .pow 2 1 2, .mul 3 2 3, .mul 3 0 3, .mul 3 1 3,
   .mul 3 0 3, .pow 2 1 2, .mul 3 2 3, .mul 3 0 3, .pow 2 1 2, .mul 3 2 3, .mul 3 0 3, .mul 3 1 3,
   .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .pow 2 1 2, .mul 3 2 3, .mul 3 0 3,
   .pow 2 1 2, .mul 3 2 3, .mul 3 0 3, .pow 2 1 2, .mul 3 2 3, .mul 3 0 3, .pow 2 1 2, .mul 3 2 3,
   .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .pow 2 1 2, .mul 3 2 3, .pow 2 1 4,
   .mul 4 0 4, .pow 2 1 2, .mul 4 2 4, .mul 4 0 4, .pow 2 1 2, .mul 4 2 4, .mul 4 0 4, .mul 4 1 4,
   .mul 4 0 4, .mul 4 1 4, .mul 4 0 4, .pow 2 1 2, .mul 4 2 4, .mul 4 0 4, .mul 4 1 4, .mul 4 0 4,
   .pow 2 1 2, .mul 4 2 4, .mul 4 0 4, .mul 4 1 4, .mul 4 0 4, .mul 4 1 4, .mul 4 0 4, .pow 2 1 2,
   .mul 4 2 4, .mul 4 0 4, .pow 2 1 2, .mul 4 2 4, .mul 4 0 4, .mul 4 1 4, .pow 2 1 5, .mul 5 0 5,
   .mul 5 1 5, .mul 5 0 5, .mul 5 1 5, .mul 5 0 5, .mul 5 1 5, .mul 5 0 5, .pow 2 1 2, .mul 5 2 5,
   .mul 5 0 5, .pow 2 1 2, .mul 5 2 5, .mul 5 0 5, .pow 2 1 2, .mul 5 2 5, .mul 5 0 5, .mul 5 1 5,
   .mul 5 0 5, .mul 5 1 5, .mul 5 0 5, .mul 5 1 5, .mul 5 0 5, .pow 2 1 2, .mul 5 2 5, .mul 5 0 5,
   .mul 5 1 5, .mul 5 0 5, .mul 5 1 5, .mul 5 0 5, .pow 2 1 2, .mul 5 2 5, .mul 5 0 5, .pow 2 1 2,
   .mul 5 2 5, .mul 5 0 5, .mul 5 1 5, .mul 5 0 5, .mul 5 1 5, .mul 5 0 5, .mul 5 1 5, .mul 5 0 5,
   .mul 5 1 5, .mul 5 0 5, .pow 2 1 2, .mul 5 2 5, .mul 5 0 5, .pow 2 1 2, .mul 5 2 5, .mul 5 0 5,
   .pow 2 1 2, .mul 5 2 5, .mul 5 0 5, .mul 5 1 5, .mul 5 0 5, .mul 5 1 5, .mul 5 0 5, .mul 5 1 5,
   .mul 5 0 5, .mul 5 1 5, .mul 5 0 5, .pow 2 1 2, .mul 5 2 5, .mul 5 0 5, .pow 2 1 2, .mul 5 2 5,
   .mul 5 0 5, .pow 2 1 2, .mul 5 2 5, .mul 5 0 5, .mul 5 1 5, .mul 5 0 5, .mul 5 1 5, .mul 5 0 5,
   .pow 2 1 2, .mul 5 2 5, .mul 5 0 5, .pow 2 1 2, .mul 5 2 5, .mul 5 0 5, .pow 2 1 2, .mul 5 2 5,
   .mul 5 0 5, .pow 2 1 2, .mul 5 2 5, .mul 5 0 5, .mul 5 1 5, .mul 5 0 5, .mul 5 1 5, .mul 5 0 5,
   .mul 5 1 5, .mul 5 0 5, .pow 1 1 6, .mul 6 0 6, .pow 2 1 2, .mul 6 2 6, .mul 6 0 6, .pow 2 1 2,
   .mul 6 2 6, .mul 6 0 6, .pow 2 1 2, .mul 6 2 6, .mul 6 0 6, .pow 2 1 2, .mul 6 2 6, .mul 6 0 6,
   .mul 6 1 6, .mul 6 0 6, .mul 6 1 6, .mul 6 0 6, .mul 6 1 6, .mul 6 0 6, .mul 6 1 6, .mul 6 0 6,
   .mul 6 1 6, .mul 6 0 6, .mul 6 1 6, .mul 6 0 6, .pow 2 1 2, .mul 6 2 6, .mul 6 0 6, .mul 6 1 6,
   .mul 6 0 6, .mul 6 1 6, .mul 6 0 6, .pow 2 1 2, .mul 6 2 6, .mul 6 0 6, .mul 6 1 6, .mul 6 0 6,
   .mul 6 1 6, .mul 6 0 6, .pow 2 1 2, .mul 6 2 6, .pow 1 1 7, .mul 7 0 7, .pow 2 1 2, .mul 7 2 7,
   .mul 7 0 7, .pow 2 1 2, .mul 7 2 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .pow 2 1 2, .mul 7 2 7,
   .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .pow 2 1 2, .mul 7 2 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7,
   .mul 7 1 7, .mul 7 0 7, .pow 2 1 2, .mul 7 2 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .pow 2 1 2,
   .mul 7 2 7, .mul 7 0 7, .pow 2 1 2, .mul 7 2 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .pow 2 1 2,
   .mul 7 2 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .pow 2 1 2, .mul 7 2 7, .mul 7 0 7, .mul 7 1 7,
   .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .mul 7 1 7,
   .mul 7 0 7, .pow 2 1 2, .mul 7 2 7, .mul 7 0 7, .pow 2 1 2, .mul 7 2 7, .mul 7 0 7, .pow 2 1 2,
   .mul 7 2 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .pow 2 1 2, .mul 7 2 7, .mul 7 0 7, .pow 2 1 2,
   .mul 7 2 7, .mul 7 0 7, .pow 2 1 2, .mul 7 2 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .mul 7 1 7,
   .mul 7 0 7, .pow 2 1 2, .mul 7 2 7, .mul 7 0 7, .pow 2 1 2, .mul 7 2 7, .mul 7 0 7, .pow 1 1 8,
   .mul 8 0 8, .pow 2 1 2, .mul 8 2 8, .mul 8 0 8, .pow 2 1 2, .mul 8 2 8, .mul 8 0 8, .mul 8 1 8,
   .mul 8 0 8, .pow 2 1 2, .mul 8 2 8, .mul 8 0 8, .pow 2 1 2, .mul 8 2 8, .mul 8 0 8, .mul 8 1 8,
   .mul 8 0 8, .mul 8 1 8, .mul 8 0 8, .pow 2 1 2, .mul 8 2 8, .mul 8 0 8, .mul 8 1 8, .mul 8 0 8,
   .pow 2 1 2, .mul 8 2 8, .mul 8 0 8, .pow 2 1 2, .mul 8 2 8, .mul 8 0 8, .mul 8 1 8, .mul 8 0 8,
   .pow 2 1 2, .mul 8 2 8, .mul 8 0 8, .pow 2 1 2, .mul 8 2 8, .mul 8 0 8, .mul 8 1 8, .mul 8 0 8,
   .mul 8 1 8, .mul 8 0 8, .pow 2 1 2, .mul 8 2 8, .mul 8 0 8, .pow 1 1 9, .mul 9 0 9, .pow 2 1 2,
   .mul 9 2 9, .mul 9 0 9, .mul 9 1 9, .mul 9 0 9, .pow 2 1 2, .mul 9 2 9, .mul 9 0 9, .pow 2 1 2,
   .mul 9 2 9, .mul 9 0 9, .pow 2 1 2, .mul 9 2 9, .mul 9 0 9, .pow 2 1 2, .mul 9 2 9, .mul 9 0 9,
   .pow 2 1 2, .mul 9 2 9, .mul 9 0 9, .pow 2 1 2, .mul 9 2 9, .mul 9 0 9, .mul 9 1 9, .mul 9 0 9,
   .mul 9 1 9, .mul 9 0 9, .mul 9 1 9, .mul 9 0 9, .pow 2 1 2, .mul 9 2 9, .mul 9 0 9, .mul 9 1 9,
   .mul 9 0 9, .pow 2 1 2, .mul 9 2 9, .mul 9 0 9, .mul 9 1 9, .mul 9 0 9, .mul 9 1 9, .mul 9 0 9,
   .mul 9 1 9, .mul 9 0 9, .mul 9 1 9, .mul 9 0 9, .pow 2 1 2, .mul 9 2 9, .mul 9 0 9, .mul 9 1 9,
   .mul 9 0 9, .mul 9 1 9, .mul 9 0 9, .pow 2 1 2, .mul 9 2 9, .mul 9 0 9, .pow 2 1 2, .mul 9 2 9,
   .mul 9 0 9, .mul 9 1 9, .mul 9 0 9, .pow 2 1 2, .mul 9 2 9, .mul 9 0 9, .mul 9 1 9, .mul 9 0 9,
   .pow 2 1 2, .mul 9 2 9, .mul 9 0 9, .mul 9 1 9, .mul 9 0 9, .mul 9 1 9, .mul 9 0 9, .pow 2 1 2,
   .mul 9 2 9, .mul 9 0 9, .mul 9 1 9, .mul 9 0 9, .pow 2 1 2, .mul 9 2 9, .mul 9 0 9, .pow 2 1 2,
   .mul 9 2 9, .mul 9 0 9, .mul 9 1 9, .mul 9 0 9, .pow 2 1 2, .mul 9 2 9, .pow 2 3 10, .pow 2 4 2,
   .mul 10 2 10, .pow 2 5 2, .mul 10 2 10]

@[expose] def cpSpec : CpSpec where
  p := 3
  m :=
    { b0 := 3, b1 := 4, b2 := 5, w0 := [(3, 1)], w1 := [(4, 1)], w2 := [(5, 1)],
      indep := [(0, 0, 1, 1), (0, 0, 2, 1), (0, 1, 0, 2), (0, 1, 1, 1), (0, 1, 2, 1), (0, 2, 0, 2),
        (0, 2, 1, 1), (0, 2, 2, 1), (1, 0, 0, 6), (1, 0, 1, 1), (1, 0, 2, 1), (1, 1, 0, 2),
        (1, 1, 1, 1), (1, 1, 2, 1), (1, 2, 0, 2), (1, 2, 1, 1), (1, 2, 2, 1), (2, 0, 0, 6),
        (2, 0, 1, 1), (2, 0, 2, 1), (2, 1, 0, 2), (2, 1, 1, 1), (2, 1, 2, 1), (2, 2, 0, 2),
        (2, 2, 1, 1), (2, 2, 2, 1)],
      acts := [{ reg := 6, ord := 3, mat := [1, 0, 1, 0, 1, 0, 0, 0, 1] },
        { reg := 7, ord := 8, mat := [0, 0, 1, 1, 2, 0, 1, 0, 2] }] }
  pts :=
    [{ reg := 10, w := [(3, 2), (4, 2), (5, 2)], t := 1,
       hs := [{ reg := 8, ord := 3, e := 1 }, { reg := 9, ord := 8, e := 2 }] }]
  rA := 0
  oA := 2
  rB := 1
  oB := 3
  wA := [(8, 1), (9, 7), (8, 2), (9, 1), (8, 2), (6, 1), (7, 7), (6, 1), (9, 7), (8, 1), (6, 1),
    (8, 1), (7, 6), (9, 7), (6, 2)]
  wB := [(7, 1), (9, 1), (7, 1), (6, 2), (8, 2), (9, 7), (6, 1), (7, 7), (6, 1), (8, 2), (9, 7),
    (8, 1), (9, 1), (8, 2)]

end CFSG.AGLEmbedding.R3.G23Three
