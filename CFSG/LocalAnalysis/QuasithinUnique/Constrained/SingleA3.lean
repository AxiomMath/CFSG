module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.Dichotomy
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.I43
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.ZTwo

public section

namespace CFSG.QuasithinUnique

theorem singleA3Excluded
    : SingleA3Excluded := by
  intro G _ _ T M H S L hcs h3 hj
  have := hcs.setting.simple
  rcases single_A3_dichotomy hcs h3 hj with ⟨U, hU4, hUexp, hUT, hC, h16⟩ |
    ⟨U, R, y, x, c, hcfg⟩
  · exact hcs.notSmall (i43_of_selfCentralizing_four hcs.setting.nonabelian
      hcs.setting.qtke.2.1 hcs.setting.sylow hUT hU4 hUexp hC h16)
  · exact zTwoConfig_false hcfg

end CFSG.QuasithinUnique
