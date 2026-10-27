module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Chevalley.LatticeCharacterInterpolation
public import CFSG.LieType.Steinberg.CentralExt.HermitianBasis
public import CFSG.LieType.Steinberg.TwistedE6.Defs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup sigma)

local instance f4PilotCTGraphRangeNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

local instance f4PilotCTGraphRangeNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

end CFSG.SeitzReduction.F4Pilot
