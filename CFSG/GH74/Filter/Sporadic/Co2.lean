module

public import CFSG.GH74.Filter.Sporadic.Spec
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Data.CFSGNative.Filter.Co2Data
public meta import Certificates.Data.CFSGNative.Filter.Co2Data
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate5025
public import CFSG.Open.Defs

public section

namespace CFSG.GH74.Filter

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem co2_secCheck :
    (ops2 22).secCheck co2Sec = true :=
  Certificates.certificate5025

theorem not_gen4_Co2 : ¬ Gen4 NativeSporadic.Co2 :=
  (spec2 22).not_gen4_of_secCheck co2Sec co2_secCheck (by decide)

end CFSG.GH74.Filter
