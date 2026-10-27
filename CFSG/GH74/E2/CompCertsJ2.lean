module

public import CFSG.GH74.Generic.NativeCerts
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public meta import Certificates.Data.CFSGNative.Filter.Sec2
public meta import Certificates.Data.CFSGNative.SectionRank.Fp
import all CFSG.Blueprint.NativeSporadic
public import CFSG.GH74.E2.CompCertsJ2Inputs
public meta import CFSG.GH74.E2.CompCertsJ2Inputs
public import Certificates.Certificate5006

public section

namespace CFSG.GH74.E2

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.GH74.Generic

theorem j2Sec_check :
    (opsP 5 14).secCheck j2Sec = true :=
  Certificates.certificate5006

theorem rankCertified_J2 : RankCertified NativeSporadic.J2 3 :=
  rankCertified_of_secCheck (specP 5 14) j2Sec j2Sec_check (by decide)

theorem rankCertified_of_isSporadic_J2 {S : Type} [Group S]
    (h : NativeSporadic.IsSporadic S .J2) : RankCertified S 3 := by
  obtain ⟨e⟩ := h
  exact rankCertified_J2.of_mulEquiv e.symm

end CFSG.GH74.E2
