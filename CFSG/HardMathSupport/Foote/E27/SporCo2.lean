module

public import CFSG.HardMathSupport.Foote.E27.SporE81
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporCo227

public section

namespace CFSG.HardMathSupport.Foote.E27

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Item434SporE81
  CFSG.Sporadic.Co2Cert

section Certificates


theorem E27Config.false_of_co2 {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}
    (h : E27Config X K R T z) (hz : z ∈ K) (e : ↥K ≃* CFSG.Blueprint.NativeSporadic.Co2) :
    False := by
  have e' : ↥K ≃* ↥co2P := e.trans co2PermEquiv
  exact h.false_of_e81Check hz co2E81 Certificates.certificate9457 (by simp [co2E81])
    (J := co2P) Item434SporCo2.pg_mem Item434SporCo2.qOrd_eq e'

theorem E27Config.false_of_sporadic_co2 {X : Type} [Group X] [Finite X] {K R T : Subgroup X}
    {z : X} (h : E27Config X K R T z) (hz : z ∈ K)
    (hbr : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier .Co2 ≃*
      (TauCeti.CFSGIndex.sporadic .Co2).Group))
    (e : ↥K ≃* (TauCeti.CFSGIndex.sporadic .Co2).Group) : False :=
  h.false_of_co2 hz (e.trans hbr.some.symm)

end Certificates

end CFSG.HardMathSupport.Foote.E27
