module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Lang.Proving.FixedOrderCongruence
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Yardstones.Md0ec50421ce4

@[expose] def isSympBCIdx : TauCeti.LieTypeIndex → Prop
  | .B _ _ => True
  | .C _ _ => True
  | _ => False

@[expose] def isOrthDIdx : TauCeti.LieTypeIndex → Prop
  | .D _ _ => True
  | .twistedD _ _ => True
  | _ => False

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
