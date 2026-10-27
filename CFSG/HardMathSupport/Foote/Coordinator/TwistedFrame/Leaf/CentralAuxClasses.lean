module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.CentralAuxF4
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.CentralAuxE6
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.CentralAuxE8Ten
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.CentralAuxE8Twelve

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.CentralAux


theorem twClassData (c : TwClass) : TwClassData c := by
  cases c
  · exact twClassData_f4Six
  · exact twClassData_e6Six
  · exact twClassData_e8Ten
  · exact twClassData_e8Twelve

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.CentralAux
