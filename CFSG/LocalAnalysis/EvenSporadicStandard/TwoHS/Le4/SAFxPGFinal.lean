module

public import Certificates.Certificate27230
public import Certificates.Certificate27231
public import Certificates.Certificate27232
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxPGMain

public section

namespace CFSG.EvenSporadicStandard.TwoHS

theorem signDataPGSpXS_proved :
    SignDataPGSpXS :=
  signDataPGSpXS_of Certificates.certificate27230.toMatrix
    Certificates.certificate27231.toMatrix Certificates.certificate27232.toMatrix

end CFSG.EvenSporadicStandard.TwoHS
