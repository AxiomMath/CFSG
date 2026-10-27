module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueFCSound
public import Certificates.Certificate25231

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

theorem fcSpec_data :
    fcSpec (uqCols uqW uqSg0) (uqCols uqW uqSg1) :=
  fcCheck_sound Certificates.certificate25231

end CFSG.EvenSporadicStandard.TwoFi22.DS81
