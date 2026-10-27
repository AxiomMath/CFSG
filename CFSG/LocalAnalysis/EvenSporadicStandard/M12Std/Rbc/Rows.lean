module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

@[expose] def RowsToChild3 : Prop :=
  M22M23M24Exclusion → J1J3J4Exclusion → HSMcLLyExclusion → TwoHSGivesHN → LargeExclusion →
    Co2Exclusion → TwoFi22Gives → TwoBGivesM → J2Exclusion → M12Co3Suz

end CFSG.EvenSporadicStandard.M12Std.Rbc
