module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.Setting

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

theorem co2Exclusion_of_kdm22
    (hKD : KDM22) : Co2Exclusion := by
  intro G _ _ L h hL
  obtain ⟨A, T, z, t, hh⟩ := exists_hyp h hL
  exact hh.false hKD

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
