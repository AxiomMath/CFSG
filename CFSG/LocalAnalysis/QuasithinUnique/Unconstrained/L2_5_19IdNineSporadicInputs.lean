module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import Certificates.Data.CFSGNative.SectionRank.Elem3

public section

namespace CFSG.QuasithinUnique.Id2519
open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint

@[expose] def j2NineData : Data where
  seedA := NativeSporadic.J2Seed1
  seedB := NativeSporadic.J2Seed2
  nregs := 61
  prog := [
      .pow 2 1 2, .mul 0 1 3, .mul 3 0 4, .mul 4 2 5, .mul 5 0 6, .mul 6 1 7, .mul 7 0 8,
      .mul 8 2 9, .mul 9 0 10, .mul 10 1 11, .mul 11 0 12, .mul 12 1 13, .mul 13 0 14,
      .mul 14 2 15, .mul 15 0 16, .mul 16 1 17, .mul 17 0 18, .mul 18 2 19, .mul 19 0 20,
      .mul 20 1 21, .mul 21 0 22, .mul 22 1 23, .mul 23 0 24, .mul 24 2 25, .mul 25 0 26,
      .mul 26 1 27, .mul 27 0 28, .mul 28 2 29, .mul 29 0 30, .mul 0 1 31, .mul 31 0 32,
      .mul 32 2 33, .mul 33 0 34, .mul 34 1 35, .mul 35 0 36, .mul 36 2 37, .mul 37 0 38,
      .mul 38 2 39, .mul 39 0 40, .mul 40 1 41, .mul 41 0 42, .mul 42 2 43, .mul 43 0 44,
      .mul 44 1 45, .mul 45 0 46, .mul 46 2 47, .mul 47 0 48, .mul 48 2 49, .mul 49 0 50,
      .mul 50 1 51, .mul 51 0 52, .mul 52 2 53, .mul 53 0 54, .mul 54 1 55, .mul 55 0 56,
      .mul 56 2 57, .mul 57 0 58, .mul 30 1 59, .mul 59 58 60
    ]
  outs := [1, 60]
  tests := List.range 14

@[expose] def hsNineData : Data where
  seedA := NativeSporadic.HSSeed1
  seedB := NativeSporadic.HSSeed2
  nregs := 53
  prog := [
      .pow 4 1 2, .mul 2 0 3, .mul 3 2 4, .mul 4 0 5, .mul 5 1 6, .mul 6 0 7, .mul 7 1 8,
      .mul 8 0 9, .mul 9 2 10, .mul 10 0 11, .pow 5 11 12, .mul 2 0 13, .mul 13 2 14, .mul 14 0 15,
      .mul 15 2 16, .mul 16 0 17, .mul 17 2 18, .mul 18 0 19, .mul 19 1 20, .mul 20 0 21,
      .mul 21 1 22, .mul 22 0 23, .mul 23 1 24, .mul 24 0 25, .mul 25 1 26, .mul 26 0 27,
      .mul 27 2 28, .mul 28 0 29, .mul 29 1 30, .mul 30 0 31, .mul 0 2 32, .mul 32 0 33,
      .mul 33 1 34, .mul 34 0 35, .mul 35 2 36, .mul 36 0 37, .mul 37 2 38, .mul 38 0 39,
      .mul 39 2 40, .mul 40 0 41, .mul 41 2 42, .mul 42 0 43, .mul 43 1 44, .mul 44 0 45,
      .mul 45 1 46, .mul 46 0 47, .mul 47 1 48, .mul 48 0 49, .mul 49 1 50, .mul 31 12 51,
      .mul 51 50 52
    ]
  outs := [12, 52]
  tests := List.range 20

end CFSG.QuasithinUnique.Id2519
