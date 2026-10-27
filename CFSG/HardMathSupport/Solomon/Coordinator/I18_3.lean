module

public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Main
public import CFSG.RankThree.PartOne.TCB.SchreierFinal

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

theorem input18_3_4_holds :
    UniquenessMaximal.Input18_3_4 :=
  input18_3_4_of_schreier CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds

end CFSG.HardMathSupport.Solomon.Coordinator
