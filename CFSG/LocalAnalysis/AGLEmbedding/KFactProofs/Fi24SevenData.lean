module

public import Certificates.Data.CFSGNative.SectionRank.Local
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.AGLEmbedding.SporCubic

open CFSG.SectionRank.Native CFSG.Blueprint

@[expose] def fi24Sylow7HData : CubData where
  seedA := NativeSporadic.Fi24primeSeed1
  seedB := NativeSporadic.Fi24primeSeed2
  nregs := 27
  prog :=
  [.pow 2 1 4, .pow 1 4 3, .mul 3 0 3, .mul 3 4 3, .mul 3 0 3, .mul 3 4 3, .mul 3 0 3, .mul 3 4 3,
    .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 4 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 4 3,
    .mul 3 0 3, .mul 3 4 3, .mul 3 0 3, .mul 3 4 3, .mul 3 0 3, .mul 3 4 3, .mul 3 0 3, .mul 3 1 3,
    .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 4 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 1 3,
    .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 1 3,
    .mul 3 0 3, .mul 3 4 3, .mul 3 0 3, .mul 3 4 3, .mul 3 0 3, .mul 3 1 3, .mul 3 0 3, .mul 3 1 3,
    .pow 1 0 5, .mul 5 4 5, .pow 2 3 2, .mul 5 2 5, .mul 5 0 5, .mul 5 3 5, .mul 5 0 5, .pow 8 3 6,
    .mul 5 6 5, .mul 5 0 5, .mul 5 6 5, .mul 5 1 5, .mul 5 0 5, .mul 5 4 5, .mul 5 3 5, .mul 5 0 5,
    .mul 5 3 5, .mul 5 1 5, .mul 5 6 5, .mul 5 1 5, .pow 7 3 2, .mul 5 2 5, .mul 5 1 5, .mul 5 0 5,
    .mul 5 4 5, .mul 5 6 5, .mul 5 4 5, .mul 5 6 5, .mul 5 4 5, .mul 5 0 5, .mul 5 6 5, .mul 5 4 5,
    .pow 7 3 2, .mul 5 2 5, .mul 5 1 5, .mul 5 0 5, .pow 1 5 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7,
    .mul 7 3 7, .pow 38 5 8, .mul 7 8 7, .mul 7 0 7, .mul 7 5 7, .mul 7 1 7, .mul 7 5 7, .mul 7 0 7,
    .mul 7 5 7, .mul 7 3 7, .mul 7 0 7, .mul 7 8 7, .mul 7 6 7, .mul 7 0 7, .mul 7 8 7, .mul 7 1 7,
    .mul 7 0 7, .mul 7 8 7, .mul 7 1 7, .mul 7 0 7, .pow 7 3 2, .mul 7 2 7, .mul 7 8 7, .pow 7 3 2,
    .mul 7 2 7, .mul 7 8 7, .pow 7 3 2, .mul 7 2 7, .mul 7 8 7, .pow 5 3 2, .mul 7 2 7, .pow 37 5 2,
    .mul 7 2 7, .mul 7 6 7, .pow 1 6 9, .pow 12 7 10, .mul 9 10 9, .pow 2 5 2, .mul 9 2 9,
    .mul 9 10 9, .mul 9 6 9, .mul 9 10 9, .mul 9 8 9, .mul 9 10 9, .mul 9 3 9, .mul 9 10 9,
    .mul 9 6 9, .mul 9 8 9, .mul 9 10 9, .mul 9 6 9, .mul 9 8 9, .mul 9 10 9, .mul 9 6 9,
    .pow 1 5 11, .mul 11 4 11, .mul 11 0 11, .mul 11 3 11, .mul 11 8 11, .pow 25 9 12,
    .mul 11 12 11, .mul 11 0 11, .mul 11 10 11, .mul 11 0 11, .mul 11 12 11, .mul 11 1 11,
    .pow 7 3 2, .mul 11 2 11, .mul 11 0 11, .pow 11 7 2, .mul 11 2 11, .mul 11 6 11, .pow 11 7 2,
    .mul 11 2 11, .mul 11 12 11, .mul 11 6 11, .mul 11 8 11, .pow 24 9 2, .mul 11 2 11, .pow 11 7 2,
    .mul 11 2 11, .pow 24 9 2, .mul 11 2 11, .mul 11 10 11, .mul 11 12 11, .mul 11 10 11,
    .pow 23 9 2, .mul 11 2 11, .mul 11 10 11, .mul 11 12 11, .pow 1 8 13, .mul 13 0 13,
    .mul 13 7 13, .pow 7 11 14, .mul 13 14 13, .mul 13 5 13, .mul 13 6 13, .mul 13 12 13,
    .pow 37 5 2, .mul 13 2 13, .mul 13 10 13, .mul 13 6 13, .mul 13 0 13, .mul 13 6 13,
    .mul 13 14 13, .mul 13 8 13, .pow 24 9 2, .mul 13 2 13, .mul 13 14 13, .mul 13 6 13,
    .pow 4 11 2, .mul 13 2 13, .mul 13 12 13, .mul 13 10 13, .pow 22 9 2, .mul 13 2 13,
    .mul 13 14 13, .mul 13 10 13, .pow 1 5 15, .mul 15 3 15, .mul 15 0 15, .mul 15 14 15,
    .mul 15 7 15, .mul 15 3 15, .pow 37 5 2, .mul 15 2 15, .mul 15 14 15, .mul 15 4 15,
    .mul 15 8 15, .mul 15 0 15, .mul 15 6 15, .mul 15 1 15, .mul 15 6 15, .pow 23 13 16,
    .mul 15 16 15, .mul 15 8 15, .mul 15 10 15, .mul 15 16 15, .mul 15 8 15, .mul 15 6 15,
    .mul 15 12 15, .mul 15 10 15, .mul 15 12 15, .mul 15 14 15, .mul 15 12 15, .mul 15 14 15,
    .pow 9 7 2, .mul 15 2 15, .pow 22 13 2, .mul 15 2 15, .mul 15 14 15, .mul 15 16 15, .pow 6 11 2,
    .mul 15 2 15, .mul 15 16 15, .pow 5 11 2, .mul 15 2 15, .mul 15 16 15, .mul 15 14 15,
    .mul 15 16 15, .mul 15 14 15, .pow 1 11 17, .mul 17 1 17, .mul 17 6 17, .mul 17 13 17,
    .mul 17 10 17, .mul 17 8 17, .mul 17 10 17, .mul 17 13 17, .mul 17 6 17, .mul 17 0 17,
    .mul 17 1 17, .mul 17 8 17, .mul 17 4 17, .mul 17 0 17, .mul 17 14 17, .mul 17 6 17,
    .pow 5 15 18, .mul 17 18 17, .mul 17 12 17, .mul 17 18 17, .mul 17 8 17, .mul 17 14 17,
    .mul 17 16 17, .mul 17 18 17, .mul 17 12 17, .mul 17 18 17, .mul 17 16 17, .mul 17 18 17,
    .mul 17 10 17, .pow 3 15 2, .mul 17 2 17, .mul 17 14 17, .pow 22 13 2, .mul 17 2 17,
    .mul 17 18 17, .mul 17 16 17, .pow 1 11 19, .pow 11 17 20, .mul 19 20 19, .pow 2 9 2,
    .mul 19 2 19, .mul 19 6 19, .mul 19 20 19, .mul 19 11 19, .mul 19 9 19, .mul 19 10 19,
    .pow 7 3 2, .mul 19 2 19, .pow 37 5 2, .mul 19 2 19, .pow 22 13 2, .mul 19 2 19, .mul 19 20 19,
    .mul 19 10 19, .mul 19 20 19, .mul 19 16 19, .mul 19 20 19, .mul 19 16 19, .pow 5 11 2,
    .mul 19 2 19, .mul 19 18 19, .pow 9 17 2, .mul 19 2 19, .pow 4 15 2, .mul 19 2 19,
    .mul 19 20 19, .mul 19 18 19, .pow 1 9 21, .mul 21 3 21, .mul 21 8 21, .mul 21 13 21,
    .mul 21 9 21, .mul 21 19 21, .mul 21 20 21, .mul 21 7 21, .mul 21 18 21, .mul 21 10 21,
    .mul 21 6 21, .mul 21 12 21, .mul 21 14 21, .mul 21 8 21, .mul 21 12 21, .mul 21 16 21,
    .pow 4 15 2, .mul 21 2 21, .mul 21 19 21, .mul 21 12 21, .mul 21 10 21, .mul 21 16 21,
    .mul 21 20 21, .pow 22 13 2, .mul 21 2 21, .mul 21 18 21, .pow 22 13 2, .mul 21 2 21,
    .mul 21 19 21, .pow 4 15 2, .mul 21 2 21, .mul 21 19 21, .pow 4 15 2, .mul 21 2 21,
    .pow 1 15 22, .pow 3 17 2, .mul 22 2 22, .mul 22 15 22, .mul 22 19 22, .mul 22 13 22,
    .mul 22 17 22, .mul 22 21 22, .mul 22 13 22, .mul 22 21 22, .mul 22 19 22, .mul 22 21 22,
    .pow 3 7 2, .mul 22 2 22, .mul 22 9 22, .mul 22 15 22, .mul 22 17 22, .mul 22 15 22,
    .mul 22 5 22, .mul 22 7 22, .mul 22 19 22, .mul 22 11 22, .mul 22 21 22, .pow 2 1 23,
    .mul 22 23 22, .mul 22 3 22, .mul 22 7 22, .mul 22 13 22, .mul 22 15 22, .mul 22 9 22,
    .pow 2 21 25, .pow 1 25 24, .mul 24 19 24, .mul 24 21 24, .mul 24 17 24, .mul 24 19 24,
    .mul 24 17 24, .mul 24 15 24, .mul 24 19 24, .mul 24 11 24, .mul 24 17 24, .mul 24 13 24,
    .mul 24 21 24, .mul 24 17 24, .mul 24 21 24, .mul 24 15 24, .mul 24 7 24, .pow 3 9 2,
    .mul 24 2 24, .mul 24 21 24, .mul 24 11 24, .mul 24 13 24, .mul 24 3 24, .mul 24 7 24,
    .mul 24 21 24, .pow 2 17 2, .mul 24 2 24, .mul 24 7 24, .mul 24 0 24, .mul 24 3 24,
    .mul 24 9 24, .mul 24 11 24, .mul 24 3 24, .pow 1 19 26, .pow 3 17 2, .mul 26 2 26, .pow 3 15 2,
    .mul 26 2 26, .pow 2 13 2, .mul 26 2 26, .mul 26 25 26, .pow 2 13 2, .mul 26 2 26, .pow 2 7 2,
    .mul 26 2 26, .mul 26 19 26, .mul 26 11 26, .mul 26 19 26, .mul 26 9 26, .mul 26 11 26,
    .mul 26 3 26, .mul 26 9 26, .mul 26 13 26, .pow 2 17 2, .mul 26 2 26, .mul 26 3 26,
    .mul 26 1 26, .mul 26 0 26, .mul 26 1 26, .mul 26 0 26]
  rx := 22
  ry := 24
  rh := 26
  r := 7
  oh := 21
  a := 2
  b := 4
  c := 0
  d := 4
  k := 1
  l := 3
  μ := 1
  t := 0

end CFSG.AGLEmbedding.SporCubic
