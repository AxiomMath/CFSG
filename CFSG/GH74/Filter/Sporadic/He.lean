module

public import CFSG.GH74.Filter.Sporadic.Spec
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import Certificates.Data.CFSGNative.Filter.HeData
public meta import Certificates.Data.CFSGNative.Filter.HeData
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate5032
public import CFSG.Open.Defs

public section

namespace CFSG.GH74.Filter

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem he_secCheck :
    (opsP 7 50).secCheck heSec = true :=
  Certificates.certificate5032

theorem not_gen4_He : ¬ Gen4 NativeSporadic.He :=
  (specP 7 50).not_gen4_of_secCheck heSec he_secCheck (by decide)

end CFSG.GH74.Filter
