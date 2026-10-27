module

public import CFSG.GH74.Generic.GKFFusion
public import CFSG.GH74.Generic.NativeCerts
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public meta import CFSG.GH74.Generic.GKFFusion
public meta import CFSG.GH74.Generic.NativeCerts
public meta import Certificates.Data.CFSGNative.Filter.Sec2
public meta import Certificates.Data.CFSGNative.SectionRank.F3
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
@[expose] def mclFus : FusData where
  seedA := include_str "../../Blueprint/Data/McLG1-f3r21B0.m1"
  seedB := include_str "../../Blueprint/Data/McLG1-f3r21B0.m2"
  nregs := 91
  prog := mclSec.prog ++ [
      .mul 2 0 47, .mul 47 3 48, .mul 48 0 49, .mul 49 3 50, .mul 50 0 51, .mul 51 4 52,
      .mul 52 0 53, .mul 53 0 54, .mul 54 0 55, .mul 55 1 56, .mul 56 0 57, .mul 57 2 58,
      .mul 58 0 59, .mul 59 2 60, .mul 60 0 61, .mul 61 3 62, .mul 1 0 63, .mul 63 4 64,
      .mul 64 0 65, .mul 65 1 66, .mul 66 0 67, .mul 67 1 68, .mul 68 0 69, .mul 69 3 70,
      .mul 70 0 71, .mul 71 0 72, .mul 72 0 73, .mul 73 2 74, .mul 74 0 75, .mul 75 4 76,
      .mul 76 0 77, .mul 77 4 78, .mul 78 0 79, .mul 79 1 80, .mul 80 0 81, .mul 81 4 82,
      .mul 4 0 83, .mul 83 1 84, .mul 84 0 85, .mul 85 0 86, .mul 86 0 87, .mul 87 4 88,
      .mul 88 0 89, .mul 89 1 90]
  o0 := 0
  o1 := 27
  o2 := 40
  o3 := 45
  sregs :=
    [62, 62, 62, 62, 62, 62, 82, 90, 62, 62, 62, 62, 62, 62, 82]
  n1s :=
    [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5]
  n2s :=
    [5, 5, 3, 3, 5, 5, 5, 5, 5, 5, 3, 3, 5, 5, 5]
  tests := [0]

end CFSG.GH74.Generic
