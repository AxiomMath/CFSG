module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.KDNPForms
public import CFSG.GroupTheory.SmallFixedTwoGroup.EightSylow

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

theorem kdnpEight_holds : KDNPEight := fun _ _ _ hE _ ht hab hcard A hA =>
  CFSG.GroupTheory.SmallFixedTwoGroup.false_of_perfect_of_centralizer_eight_of_alt5 hE ht hab
    hcard A hA

end CFSG.EvenSporadicStandard.M12Std.Rbc
