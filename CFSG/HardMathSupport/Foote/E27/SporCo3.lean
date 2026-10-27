module

public import CFSG.HardMathSupport.Foote.E27.LieTwo.Kill
public import Certificates.Certificate131000
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Kit
public import CFSG.Sporadic.Schreier.Co3Faithful
public import Certificates.Data.TripleCoverLift.HN

public section

namespace CFSG.HardMathSupport.Foote.E27

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Item434SporE81
open CFSG.Sporadic.Schreier.Co3 (co3P co3PermEquiv)

section Certificates

theorem E27Config.false_of_co3 {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}
    (h : E27Config X K R T z) (hz : z ∈ K) (e : ↥K ≃* CFSG.Blueprint.NativeSporadic.Co3) :
    False := by
  have e' : ↥K ≃* ↥co3P := e.trans co3PermEquiv
  obtain ⟨S, hS, hprop⟩ := Certificates.certificate131000
  exact h.false_of_sylow_table hz e' S hS hprop

theorem E27Config.false_of_sporadic_co3 {X : Type} [Group X] [Finite X] {K R T : Subgroup X}
    {z : X} (h : E27Config X K R T z) (hz : z ∈ K)
    (hbr : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier .Co3 ≃*
      (TauCeti.CFSGIndex.sporadic .Co3).Group))
    (e : ↥K ≃* (TauCeti.CFSGIndex.sporadic .Co3).Group) : False :=
  h.false_of_co3 hz (e.trans hbr.some.symm)

end Certificates

end CFSG.HardMathSupport.Foote.E27
