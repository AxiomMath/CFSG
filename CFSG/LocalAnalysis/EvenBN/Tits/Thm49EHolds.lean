module

public import Certificates.Certificate28042
public import Certificates.Certificate28043
public import CFSG.LocalAnalysis.EvenBN.Tits.Thm49EMain
public import CFSG.LocalAnalysis.EvenBN.Tits.Thm49ETOK

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Thm49E

theorem f6Facts_holds :
    F6Facts zpHat y0Hat :=
  f6Facts_of_k Certificates.certificate28042.choose_spec

theorem toHat_holds :
    TOHat zpHat y0Hat :=
  toHat_of_k labFacts (f6Facts_of_k Certificates.certificate28042.choose_spec)
    (kcard_of_k Certificates.certificate28042.choose_spec)
    Certificates.certificate28043.choose_spec.choose_spec.choose_spec

theorem thm49FailureExclusion_holds :
    Thm49FailureExclusion :=
  thm49FailureExclusion_of_facts f6Facts_holds toHat_holds

end CFSG.LocalAnalysis.EvenBN.Tits.Thm49E
