module

public import CFSG.GH74.Generic.NativeCerts
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public meta import Certificates.Data.CFSGNative.Filter.Sec2
public meta import Certificates.Data.CFSGNative.SectionRank.F2
import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.GH74.E2

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.GH74.Generic
@[expose] def j3Sec : SecData where
  seedA := include_str "../../Blueprint/Data/J3G1-f2r80B0.m1"
  seedB := include_str "../../Blueprint/Data/J3G1-f2r80B0.m2"
  nregs := 96
  prog := [
      .pow 2 1 2, .mul 2 0 3, .mul 3 1 4, .mul 4 0 5, .mul 5 2 6, .mul 6 0 7, .mul 7 2 8,
      .mul 8 0 9, .mul 9 2 10, .mul 10 0 11, .mul 11 1 12, .mul 12 0 13, .mul 13 2 14,
      .mul 14 0 15, .mul 15 1 16, .mul 16 0 17, .mul 17 2 18, .mul 18 0 19, .mul 19 1 20,
      .mul 20 0 21, .mul 21 1 22, .mul 22 0 23, .mul 23 1 24, .mul 24 0 25, .mul 25 2 26,
      .mul 26 0 27, .mul 27 1 28, .mul 5 1 29, .mul 29 0 30, .mul 30 2 31, .mul 31 0 32,
      .mul 32 2 33, .mul 33 0 34, .mul 34 1 35, .mul 35 0 36, .mul 36 1 37, .mul 37 0 38,
      .mul 38 1 39, .mul 39 0 40, .mul 40 1 41, .mul 41 0 42, .mul 42 2 43, .mul 43 0 44,
      .mul 44 2 45, .mul 45 0 46, .mul 46 2 47, .mul 47 0 48, .mul 48 2 49, .mul 49 0 50,
      .mul 50 1 51, .mul 51 0 52, .mul 52 1 53, .mul 53 0 54, .mul 54 2 55, .mul 55 0 56,
      .mul 56 2 57, .mul 57 0 58, .mul 58 1 59, .mul 9 1 60, .mul 60 0 61, .mul 61 1 62,
      .mul 62 0 63, .mul 63 1 64, .mul 64 0 65, .mul 65 2 66, .mul 66 0 67, .mul 67 2 68,
      .mul 68 0 69, .mul 69 2 70, .mul 70 0 71, .mul 71 2 72, .mul 72 0 73, .mul 73 1 74,
      .mul 74 0 75, .mul 75 1 76, .mul 76 0 77, .mul 77 1 78, .mul 78 0 79, .mul 79 1 80,
      .mul 80 0 81, .mul 81 2 82, .mul 82 0 83, .mul 83 2 84, .mul 84 0 85, .mul 85 2 86,
      .mul 86 0 87, .mul 87 1 88, .mul 88 0 89, .mul 89 1 90, .mul 90 0 91, .mul 91 2 92,
      .mul 92 0 93, .mul 93 1 94]
  outs := [0, 28, 59, 94]
  tReg := 95
  tests := List.range 80
end CFSG.GH74.E2
