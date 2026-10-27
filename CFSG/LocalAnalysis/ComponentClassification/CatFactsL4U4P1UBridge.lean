
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1UBridgeBase

public import Certificates.Certificate22241

public section

namespace CFSG.ComponentClassification.HarrisLit.P1.U43

open CFSG.LieType.Multipliers.U43 Matrix Subgroup CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native

theorem centTriv_check : centTrivOK 820 uSift u43CentTriv = true :=
  Certificates.certificate22241

theorem eq_one_of_commute_psi {c : Equiv.Perm (Fin 820)} (hc : ∀ g, c * psi g = psi g * c) :
    c = 1 :=
  eq_one_of_centTrivOK u43_groupData centTriv_check (by rintro _ ⟨g, rfl⟩; exact hc g)

end CFSG.ComponentClassification.HarrisLit.P1.U43
