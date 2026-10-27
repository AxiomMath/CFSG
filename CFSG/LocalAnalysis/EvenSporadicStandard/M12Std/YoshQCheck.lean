module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshLemma5ModelCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshL7Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshSylowHomCheck

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

@[expose] def modelFactsCheck : Bool :=
  fusionCheck &&
    [0, 1].all (fun α => [0, 1].all fun k => ueCheck α k && esCheck α k) &&
    [0, 1].all (fun k => l6Check 0 k) &&
    [0, 1].all (fun k => l7Check 1 k && l8Check 1 k) &&
    sylowHomCheckAll

@[expose] def yoshQCheck : Bool :=
  lemma4Check && lemma5Check && lemma5ModelCheck && modelFactsCheck

end CFSG.EvenSporadicStandard.M12Std.Yosh
