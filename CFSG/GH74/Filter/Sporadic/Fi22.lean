module

public import CFSG.GH74.Filter.Sporadic.Spec
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import Certificates.Data.CFSGNative.Filter.Fi22Data
public meta import Certificates.Data.CFSGNative.Filter.Fi22Data
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate5027
public import CFSG.Open.Defs

public section

namespace CFSG.GH74.Filter

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem fi22_secCheck :
    (ops3 77).secCheck fi22Sec = true :=
  Certificates.certificate5027

theorem not_gen4_Fi22 : ¬ Gen4 NativeSporadic.Fi22 :=
  (spec3 77).not_gen4_of_secCheck fi22Sec fi22_secCheck (by decide)

end CFSG.GH74.Filter
