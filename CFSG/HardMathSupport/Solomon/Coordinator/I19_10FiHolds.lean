module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10FiWeak
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10Red

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

theorem weakFi22Five_holds :
    WeakFi22Five :=
  fun S _ _ hS hnab hFi A hA => weakFi22FiveElem_holds S hS hnab hFi A hA

end CFSG.HardMathSupport.Solomon.Coordinator
