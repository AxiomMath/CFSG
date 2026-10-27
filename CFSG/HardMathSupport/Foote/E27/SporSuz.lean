module

public import CFSG.HardMathSupport.Foote.E27.SporE81
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporSuz27

public section

namespace CFSG.HardMathSupport.Foote.E27

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Item434SporE81
  CFSG.Sporadic.SuzOddCore

section Certificates


theorem E27Config.false_of_suz {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}
    (h : E27Config X K R T z) (hz : z ∈ K) (e : ↥K ≃* CFSG.Blueprint.NativeSporadic.Suz) :
    False := by
  have e' : ↥K ≃* ↥suzM := e.trans suzEquivM
  exact h.false_of_e81Check hz suzE81 Certificates.certificate9458 (by simp [suzE81])
    (J := suzM) Item434SporSuz.pg_mem Item434SporSuz.qOrd_eq e'

theorem E27Config.false_of_sporadic_suz {X : Type} [Group X] [Finite X] {K R T : Subgroup X}
    {z : X} (h : E27Config X K R T z) (hz : z ∈ K)
    (hbr : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier .Suz ≃*
      (TauCeti.CFSGIndex.sporadic .Suz).Group))
    (e : ↥K ≃* (TauCeti.CFSGIndex.sporadic .Suz).Group) : False :=
  h.false_of_suz hz (e.trans hbr.some.symm)

end Certificates

end CFSG.HardMathSupport.Foote.E27
