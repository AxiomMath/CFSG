module

public import CFSG.GH74.Filter.Sporadic.Spec
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import Certificates.Data.CFSGNative.Filter.HNData
public meta import Certificates.Data.CFSGNative.Filter.HNData
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate5030
public import CFSG.Open.Defs

public section

namespace CFSG.GH74.Filter

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem hn_secCheck :
    (opsP 5 133).secCheck hnSec = true :=
  Certificates.certificate5030

theorem not_gen4_HN : ¬ Gen4 NativeSporadic.HN :=
  (specP 5 133).not_gen4_of_secCheck hnSec hn_secCheck (by decide)

end CFSG.GH74.Filter
