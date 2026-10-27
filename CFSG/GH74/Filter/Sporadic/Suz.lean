module

public import CFSG.GH74.Filter.Sporadic.Spec
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import Certificates.Data.CFSGNative.Filter.SuzData
public meta import Certificates.Data.CFSGNative.Filter.SuzData
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate5036
public import CFSG.Open.Defs

public section

namespace CFSG.GH74.Filter

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem suz_secCheck :
    (ops3 64).secCheck suzSec = true :=
  Certificates.certificate5036

theorem not_gen4_Suz : ¬ Gen4 NativeSporadic.Suz :=
  (spec3 64).not_gen4_of_secCheck suzSec suz_secCheck (by decide)

end CFSG.GH74.Filter
