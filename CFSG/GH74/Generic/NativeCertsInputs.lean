module

public import CFSG.GH74.Filter.Sporadic.Spec
public import CFSG.GH74.Generic.Certificates
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public meta import Certificates.Data.CFSGNative.Filter.Sec2
public meta import Certificates.Data.CFSGNative.SectionRank.F3
public meta import Certificates.Data.CFSGNative.SectionRank.Fp
import CFSG.Blueprint.NativeSporadic
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

public section

namespace CFSG.GH74.Generic

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native
@[expose] def mclSec : SecData where
  seedA := include_str "../../Blueprint/Data/McLG1-f3r21B0.m1"
  seedB := include_str "../../Blueprint/Data/McLG1-f3r21B0.m2"
  nregs := 47
  prog := [
      .pow 2 1 2, .pow 3 1 3, .pow 4 1 4, .mul 0 1 5, .mul 5 0 6, .mul 6 1 7, .mul 7 0 8,
      .mul 8 4 9, .mul 9 0 10, .mul 0 1 11, .mul 11 0 12, .mul 12 3 13, .mul 13 0 14, .mul 14 2 15,
      .mul 15 0 16, .mul 0 4 17, .mul 17 0 18, .mul 18 3 19, .mul 19 0 20, .mul 20 1 21, .mul 21 0 22,
      .pow 5 16 23, .mul 0 23 24, .mul 24 0 25, .mul 25 16 26, .pow 2 26 27, .pow 4 10 28,
      .mul 0 28 29, .mul 29 0 30, .mul 30 10 31, .pow 3 31 32, .pow 4 22 33, .mul 0 33 34,
      .mul 34 0 35, .mul 35 22 36, .mul 22 36 37, .mul 27 32 38, .mul 38 27 39, .mul 39 32 40,
      .pow 4 37 41, .mul 27 41 42, .mul 42 27 43, .mul 43 37 44, .pow 2 44 45]
  outs := [0, 27, 40, 45]
  tReg := 46
  tests := [0]

@[expose] def lySec : SecData where
  seedA := include_str "../../Blueprint/Data/LyG1-f5r111B0.m1"
  seedB := include_str "../../Blueprint/Data/LyG1-f5r111B0.m2"
  nregs := 50
  prog := [
      .pow 2 1 2, .pow 3 1 3, .pow 4 1 4, .mul 0 3 5, .mul 5 0 6, .mul 6 2 7, .mul 7 0 8,
      .mul 8 1 9, .mul 9 0 10, .mul 0 4 11, .mul 11 0 12, .mul 12 2 13, .mul 13 0 14, .mul 14 4 15,
      .mul 15 0 16, .mul 0 1 17, .mul 17 0 18, .mul 18 4 19, .mul 19 0 20, .mul 20 1 21, .mul 21 0 22,
      .pow 30 16 23, .mul 0 23 24, .mul 24 0 25, .mul 25 16 26, .pow 6 26 27, .pow 66 10 28,
      .mul 0 28 29, .mul 29 0 30, .mul 30 10 31, .pow 33 31 32, .mul 10 32 33, .pow 66 22 34,
      .mul 0 34 35, .mul 35 0 36, .mul 36 22 37, .mul 22 37 38, .pow 7 33 39, .mul 27 39 40,
      .mul 40 27 41, .mul 41 33 42, .pow 4 42 43, .pow 29 38 44, .mul 27 44 45, .mul 45 27 46,
      .mul 46 38 47, .pow 2 47 48]
  outs := [0, 27, 43, 48]
  tReg := 49
  tests := [0]

end CFSG.GH74.Generic
