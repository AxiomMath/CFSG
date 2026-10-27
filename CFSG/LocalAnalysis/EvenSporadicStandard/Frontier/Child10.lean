module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Contract
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44Final

public section

namespace CFSG.EvenSporadicStandard.Frontier

open CFSG.Blueprint.NativeSporadic

theorem child10_of_frontier
    (hFi24 : TwoFi22.DS81.Fi24RecognitionLocal) :
    TwoFi22Gives :=
  twoFi22Gives_of_branch
    (TwoFi22.DS81.fi24Branch_of_stage44_local
      (TwoFi22.DS81.stage44'_final
        (TwoFi22.DS81.fi22CoverRest_of_aut TwoFi22.DS81.fi22CoverAut))
      hFi24)

end CFSG.EvenSporadicStandard.Frontier
