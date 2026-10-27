module

public import CFSG.GH74.KGroups.CoverJ3Check
public import CFSG.GH74.KGroups.CoverE16
public import CFSG.GH74.KGroups.CoverRank
public import CFSG.GH74.KGroups.Generic5
public import CFSG.GH74.Generic.Shapes
public meta import CFSG.GH74.KGroups.CoverJ3Check
public meta import Certificates.Data.CFSGNative.Filter.Sec2
public meta import Certificates.Data.CFSGNative.SectionRank.F2
import CFSG.Blueprint.NativeSporadic
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.SectionRank.CentralLift
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public meta import CFSG.Open.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

public section

namespace CFSG.GH74.KGroups.J3

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native
set_option compiler.extract_closed false

@[expose] def j3Words : List (List ℤ) :=
    [[], [-2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1,
    2], [2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2], [2, 1, 2,
    1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2], [-2,
    1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2], [-2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1,
    2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2], [-2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1,
    -2, 1, 2, 1, 2, 1, 2, 1, -2], [-2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1,
    2, 1, 2, 1, 2, 1, 2], [-2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1,
    -2], [-2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2], [-2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1,
    2, 1, -2, 1, 2], [2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2,
    1, 2, 1, -2], [-2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2,
    1, 2], [-2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2,
    1, 2, 1, -2], [-2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1,
    2]]

end CFSG.GH74.KGroups.J3
