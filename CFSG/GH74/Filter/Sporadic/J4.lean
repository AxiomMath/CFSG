module

public import CFSG.GH74.Filter.Sporadic.Spec
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Data.CFSGNative.Filter.J4Data
public meta import Certificates.Data.CFSGNative.Filter.J4Data
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate5033
public import CFSG.Open.Defs

public section

namespace CFSG.GH74.Filter

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem j4_secCheck :
    (ops2 112).secCheck j4Sec = true :=
  Certificates.certificate5033

theorem not_gen4_J4 : ¬ Gen4 NativeSporadic.J4 :=
  (spec2 112).not_gen4_of_secCheck j4Sec j4_secCheck (by decide)

end CFSG.GH74.Filter
