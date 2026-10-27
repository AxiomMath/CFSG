module

public import CFSG.GH74.E2.KRest
public import CFSG.GH74.KGroups.TwoM12Fixed
public import CFSG.GH74.KGroups.TwoM12Syl3

public section

namespace CFSG.GH74.KGroups.TwoM12

theorem twoM12Facts
    : CFSG.GH74.E2.TwoM12Facts where
  autRank_ge5 := by
    intro K _ _ h p hp h5 B hB
    exact autRank_ge5_of_shape2M12 h p hp h5 B hB
  autRank3_le_two := by
    intro K _ _ h R hR
    exact autRank3_le_two_of_shape2M12 h R hR
  autCentralizer := by
    intro K _ _ h R _ hc ψ hψ hψc
    exact autCentralizer_of_shape2M12 h R hc ψ hψ hψc
  pumpUp := by
    intro K _ _ h α hα2 hα1 L hL hq
    exact pumpUp_of_shape2M12 h α hα2 hα1 L hL hq

end CFSG.GH74.KGroups.TwoM12
