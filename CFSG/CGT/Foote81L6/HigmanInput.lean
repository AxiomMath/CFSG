module

public import CFSG.CGT.Foote81L6.Normalizer.Identify
public import CFSG.CGT.Higman76.Higman

public section

namespace CFSG.CGT.Foote81L6

theorem higmanHyp_holds
    : Normalizer.HigmanHyp := by
  intro G _ _ S a ha haS hgen h2
  exact CFSG.CGT.Higman76.higman S ha haS hgen h2

end CFSG.CGT.Foote81L6
