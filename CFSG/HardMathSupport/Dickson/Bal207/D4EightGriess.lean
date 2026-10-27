module

public import CFSG.HardMathSupport.Dickson.Bal207.FamD4EightShape
import CFSG.HardMathSupport.Dickson.Bal207.OrthInnerShape
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux

theorem bal207PlusFamD4Eight_of_griess (hGA : GriessAllModelsStatement) :
    Bal207PlusFamD4Eight NonSemilinD4Eight :=
  bal207PlusFamD4Eight_of_orthInnerShape OrthFix.orthInnerShape hGA

end CFSG.HardMathSupport.Dickson.Bal207

end
