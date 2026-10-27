module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.P12Gen
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.P12Sound
public import Certificates.Certificate450015
public import Certificates.Certificate450016

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK

theorem p12Facts_of_certs :
    P12Facts where
  sylow := sylowData_elemFactsIn (card_alt_two_part (Or.inl rfl))
    (P12.p12Check_sound Certificates.certificate450015)
  alt12 := sylowData_nine (card_alt_two_part (Or.inl rfl))
    (P12.p12Check_sound Certificates.certificate450015)
  alt13 := sylowData_nine (card_alt_two_part (Or.inr rfl))
    (P12.p12Check_sound Certificates.certificate450016)

end CFSG.EvenSporadicStandard.M12Std.SolomonK
