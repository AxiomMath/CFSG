module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzJtF2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzJtF3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzJtF4
public import Certificates.Certificate441783

public section

namespace CFSG.OddStandard.SmallF3.FritzII

theorem fzJFailsR3_holds : FzJFailsR3 :=
  fzJFailsR3_of_model
    (Certificates.FzJt.fzJtCheck_sound Certificates.certificate441783).1

theorem fzCalZPairR3_holds : FzCalZPairR3 :=
  fzCalZPairR3_of_model
    (Certificates.FzJt.fzJtCheck_sound Certificates.certificate441783).2.1

theorem fzJtWitness_holds : FzJtWitness :=
  fzJtWitness_of_model
    (Certificates.FzJt.fzJtCheck_sound Certificates.certificate441783).2.2

end CFSG.OddStandard.SmallF3.FritzII
