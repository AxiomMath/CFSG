module

public import CFSG.GH74.Filter.Sporadic.Spec
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Data.CFSGNative.Filter.Co1Data
public meta import Certificates.Data.CFSGNative.Filter.Co1Data
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate5024
public import CFSG.Open.Defs

public section

namespace CFSG.GH74.Filter

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem co1_secCheck :
    (ops2 24).secCheck co1Sec = true :=
  Certificates.certificate5024

theorem not_gen4_Co1 : ¬ Gen4 NativeSporadic.Co1 :=
  (spec2 24).not_gen4_of_secCheck co1Sec co1_secCheck (by decide)

end CFSG.GH74.Filter
