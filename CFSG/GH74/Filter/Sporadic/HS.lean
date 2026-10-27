module

public import CFSG.GH74.Filter.Sporadic.Spec
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Data.CFSGNative.Filter.HSData
public meta import Certificates.Data.CFSGNative.Filter.HSData
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate5031
public import CFSG.Open.Defs

public section

namespace CFSG.GH74.Filter

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem hs_secCheck :
    (ops2 20).secCheck hsSec = true :=
  Certificates.certificate5031

theorem not_gen4_HS : ¬ Gen4 NativeSporadic.HS :=
  (spec2 20).not_gen4_of_secCheck hsSec hs_secCheck (by decide)

end CFSG.GH74.Filter
