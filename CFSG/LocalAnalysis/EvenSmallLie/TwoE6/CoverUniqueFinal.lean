module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.CoverUnique
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.LeviA2DiagInput
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate82
public import Certificates.Certificate83
public import Certificates.Certificate84
public import Certificates.Certificate85
public import Certificates.Certificate86
public import Certificates.Certificate87
public import Certificates.Certificate88
public import Certificates.Certificate89
public import Certificates.Certificate90
public import Certificates.Certificate91
public import Certificates.Certificate92
public import Certificates.Certificate93
public import Certificates.Certificate94
public import Certificates.Certificate95
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate110
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate6023
public import Certificates.Certificate6024
public import Certificates.Certificate3023
public import Certificates.Certificate3043
public import Certificates.Certificate3130
public import Certificates.Certificate3131
public import Certificates.Certificate3132
public import Certificates.Certificate3133
public import Certificates.Certificate3134
public import Certificates.Certificate3135
public import Certificates.Certificate3136
public import Certificates.Certificate3137
public import Certificates.Certificate3178
public import Certificates.Certificate3179
public import Certificates.Certificate8046
public import Certificates.Certificate8048
public import Certificates.Certificate8049
public import Certificates.Certificate8052
public import Certificates.Certificate10032
public import Certificates.Certificate10033
public import Certificates.Certificate10034
public import Certificates.Certificate10035
public import Certificates.Certificate10069
public import Certificates.Certificate10070
public import Certificates.Certificate16005

public section

namespace CFSG.EvenSmallLie.TwoE6

theorem doubleCoverUnique
    : DoubleCoverUnique :=
  doubleCoverUnique_of_inputs leviA2DiagInput

theorem coverOuterLeTwo
    : CoverOuterLeTwo :=
  coverOuterLeTwo_of_inputs leviA2DiagInput

theorem child2E6_of_stroth
    (h21 : Stroth21) (h23 : Stroth23) : Child2E6 :=
  child2E6_of_inputs doubleCoverUnique coverOuterLeTwo h21 h23

end CFSG.EvenSmallLie.TwoE6
