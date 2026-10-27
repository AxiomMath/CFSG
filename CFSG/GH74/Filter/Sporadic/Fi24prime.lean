module

public import CFSG.GH74.Filter.Sporadic.Spec
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import Certificates.Data.CFSGNative.Filter.Fi24primeData
public meta import Certificates.Data.CFSGNative.Filter.Fi24primeData
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate5029
public import CFSG.Open.Defs

public section

namespace CFSG.GH74.Filter

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem fi24prime_secCheck :
    (ops3 781).secCheck fi24primeSec = true :=
  Certificates.certificate5029

theorem not_gen4_Fi24prime : ¬ Gen4 NativeSporadic.Fi24prime :=
  (spec3 781).not_gen4_of_secCheck fi24primeSec fi24prime_secCheck (by decide)

end CFSG.GH74.Filter
