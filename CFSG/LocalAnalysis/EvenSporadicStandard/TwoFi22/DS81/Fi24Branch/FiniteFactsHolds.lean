module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeHolds
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Core
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBFactsHolds
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.U42Holds

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

theorem finiteFacts_holds :
    FiniteFacts :=
  ⟨cocodeFacts_holds, kFacts_holds, u42Facts_holds⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
