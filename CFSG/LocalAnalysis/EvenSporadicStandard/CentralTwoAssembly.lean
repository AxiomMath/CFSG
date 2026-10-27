module

public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoM23
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoHS
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoCo2
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoJ3
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoM22
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoFischer
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoTh
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoONan

public section

namespace CFSG.EvenSporadicStandard

theorem centralTwoBound_of_rowBound_HN
    (hHN : RowBound .HN) : CentralTwoBound :=
  centralTwoBound_of_rows fun s => by
    cases s
    all_goals first
      | exact rowBound_M11
      | exact rowBound_J1
      | exact rowBound_M12
      | exact rowBound_J2
      | exact rowBound_M24
      | exact rowBound_J4
      | exact rowBound_McL
      | exact rowBound_He
      | exact rowBound_Ru
      | exact rowBound_Suz
      | exact rowBound_M
      | exact rowBound_B
      | exact rowBound_Co1
      | exact rowBound_Ly
      | exact rowBound_Co3
      | exact rowBound_M23
      | exact rowBound_HS
      | exact rowBound_Co2
      | exact rowBound_J3
      | exact rowBound_M22
      | exact rowBound_Fi22
      | exact rowBound_Fi23
      | exact rowBound_Fi24Prime
      | exact rowBound_Th
      | exact rowBound_ONan
      | exact hHN

end CFSG.EvenSporadicStandard
