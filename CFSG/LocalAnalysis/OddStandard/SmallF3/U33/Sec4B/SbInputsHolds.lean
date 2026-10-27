module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbInputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23Main

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open CFSG.OddStandard.SmallF3.HarrisU33.GH23Data CFSG.OddStandard.SmallF3.HarrisU33.Outside

theorem sec4BInputs_holds :
    Sec4BInputs :=
  ⟨Outside.ghii23List_holds⟩

end CFSG.OddStandard.SmallF3.HarrisU33
