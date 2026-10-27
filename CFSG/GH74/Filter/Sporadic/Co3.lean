module

public import CFSG.GH74.Filter.Sporadic.Spec
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Data.CFSGNative.Filter.Co3Data
public meta import Certificates.Data.CFSGNative.Filter.Co3Data
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate5026
public import CFSG.Open.Defs

public section

namespace CFSG.GH74.Filter

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem co3_secCheck :
    (ops2 22).secCheck co3Sec = true :=
  Certificates.certificate5026

theorem not_gen4_Co3 : ¬ Gen4 NativeSporadic.Co3 :=
  (spec2 22).not_gen4_of_secCheck co3Sec co3_secCheck (by decide)

end CFSG.GH74.Filter
