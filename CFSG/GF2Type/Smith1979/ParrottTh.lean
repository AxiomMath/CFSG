module

public import CFSG.Sporadic.Th.Recog.Glue
public import CFSG.GF2Type.Smith1979.WidthFourKPLeaves

public section

namespace CFSG.GF2Type.Smith1979

open CFSG.Sporadic.Th.Recog


theorem parrottThKP_of_glueMFacts (hBB : A9FaithfulDimEight) (hMF : GlueMFacts) :
    ParrottThKP := by
  intro G _ _ _ _ _ _ z hz hext hcard hwc Mbar _ hM ⟨e⟩
  exact isSporadic_th_of_setting (ThSetting.ofLeaf hz hext hcard hwc hM e) hBB hMF

end CFSG.GF2Type.Smith1979
