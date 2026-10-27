module

public import CFSG.GH74.Filter.Sporadic.Spec
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Data.CFSGNative.Filter.RuData
public meta import Certificates.Data.CFSGNative.Filter.RuData
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate5035
public import CFSG.Open.Defs

public section

namespace CFSG.GH74.Filter

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem ru_secCheck :
    (ops2 28).secCheck ruSec = true :=
  Certificates.certificate5035

theorem not_gen4_Ru : ¬ Gen4 NativeSporadic.Ru :=
  (spec2 28).not_gen4_of_secCheck ruSec ru_secCheck (by decide)

end CFSG.GH74.Filter
