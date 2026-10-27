module

public import CFSG.GH74.Filter.Sporadic.Spec
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import Certificates.Data.CFSGNative.Filter.Fi23Data
public meta import Certificates.Data.CFSGNative.Filter.Fi23Data
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate5028
public import CFSG.Open.Defs

public section

namespace CFSG.GH74.Filter

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem fi23_secCheck :
    (ops3 253).secCheck fi23Sec = true :=
  Certificates.certificate5028

theorem not_gen4_Fi23 : ¬ Gen4 NativeSporadic.Fi23 :=
  (spec3 253).not_gen4_of_secCheck fi23Sec fi23_secCheck (by decide)

end CFSG.GH74.Filter
