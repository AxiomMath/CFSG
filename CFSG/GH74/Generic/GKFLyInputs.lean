module

public import CFSG.GH74.Generic.GKFFusion
public import CFSG.GH74.Generic.NativeCerts
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public meta import CFSG.GH74.Generic.GKFFusion
public meta import CFSG.GH74.Generic.NativeCerts
public meta import Certificates.Data.CFSGNative.Filter.Sec2
public meta import Certificates.Data.CFSGNative.SectionRank.Fp
import CFSG.Blueprint.NativeSporadic
public meta import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GH74.Generic.Shapes
public meta import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Statements
public meta import CFSG.GH74.Statements
public import CFSG.LieType.CurtisTits.Conclusion
public meta import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public meta import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public meta import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public meta import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public meta import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.GH74.Generic.Fusion Subgroup
@[expose] def lyFus : FusData where
  seedA := include_str "../../Blueprint/Data/LyG1-f5r111B0.m1"
  seedB := include_str "../../Blueprint/Data/LyG1-f5r111B0.m2"
  nregs := 118
  prog := lySec.prog ++ [
      .mul 2 0 50, .mul 50 3 51, .mul 51 0 52, .mul 52 3 53, .mul 53 0 54, .mul 54 4 55,
      .mul 55 0 56, .mul 56 0 57, .mul 57 0 58, .mul 58 1 59, .mul 59 0 60, .mul 60 2 61,
      .mul 61 0 62, .mul 62 2 63, .mul 63 0 64, .mul 64 3 65, .mul 3 0 66, .mul 66 3 67,
      .mul 67 0 68, .mul 68 1 69, .mul 69 0 70, .mul 70 2 71, .mul 71 0 72, .mul 72 0 73,
      .mul 73 0 74, .mul 74 3 75, .mul 75 0 76, .mul 76 4 77, .mul 77 0 78, .mul 78 2 79,
      .mul 79 0 80, .mul 80 2 81, .mul 3 0 82, .mul 82 2 83, .mul 83 0 84, .mul 84 4 85,
      .mul 85 0 86, .mul 86 4 87, .mul 87 0 88, .mul 88 3 89, .mul 89 0 90, .mul 90 0 91,
      .mul 91 0 92, .mul 92 2 93, .mul 93 0 94, .mul 94 1 95, .mul 95 0 96, .mul 96 1 97,
      .mul 97 0 98, .mul 98 3 99, .mul 99 0 100, .mul 100 2 101, .mul 4 0 102, .mul 102 4 103,
      .mul 103 0 104, .mul 104 1 105, .mul 105 0 106, .mul 106 4 107, .mul 107 0 108,
      .mul 108 0 109, .mul 109 0 110, .mul 110 1 111, .mul 111 0 112, .mul 112 4 113,
      .mul 113 0 114, .mul 114 1 115, .mul 115 0 116, .mul 116 1 117]
  o0 := 0
  o1 := 27
  o2 := 43
  o3 := 48
  sregs :=
    [65, 65, 81, 65, 81, 101, 65, 65, 65, 117, 65, 65, 65, 65, 65]
  n1s :=
    [7, 7, 15, 7, 15, 67, 7, 7, 7, 31, 7, 7, 7, 7, 7]
  n2s :=
    [7, 67, 21, 67, 31, 37, 31, 15, 31, 31, 31, 31, 21, 37, 31]
  tests := [0]

end CFSG.GH74.Generic
