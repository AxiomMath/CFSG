module

public import CFSG.GH74.Generic.NativeCerts
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public meta import Certificates.Data.CFSGNative.Filter.Sec2
public meta import Certificates.Data.CFSGNative.SectionRank.F2
import all CFSG.Blueprint.NativeSporadic
public import CFSG.GH74.E2.CompCertsJ3Inputs
public meta import CFSG.GH74.E2.CompCertsJ3Inputs
public import Certificates.Certificate5007

public section

namespace CFSG.GH74.E2

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.GH74.Generic

theorem j3Sec_check :
    (ops2 80).secCheck j3Sec = true :=
  Certificates.certificate5007

theorem rankCertified_J3 : RankCertified NativeSporadic.J3 3 :=
  rankCertified_of_secCheck (spec2 80) j3Sec j3Sec_check (by decide)

theorem rankCertified_of_isSporadic_J3 {S : Type} [Group S]
    (h : NativeSporadic.IsSporadic S .J3) : RankCertified S 3 := by
  obtain ⟨e⟩ := h
  exact rankCertified_J3.of_mulEquiv e.symm

end CFSG.GH74.E2
