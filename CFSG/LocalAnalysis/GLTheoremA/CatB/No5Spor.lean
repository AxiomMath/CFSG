module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.No5Arith
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20BigBM
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Coordinator.SporOrders
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.No5

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator

section Spor


theorem no5_spor {Y : Type} [Group Y] [Finite Y] (s : TauCeti.SporadicName)
    (e : Y ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hBM : NoOrderSixtyFiveBM)
    {y : Y} (hy : orderOf y = 5) {J : Subgroup Y} (hJ : GLAPComponent 5 (S8.cx y) J)
    (hcard : Nat.card (PSimple 5 J) = CFSG.Open.orderCo1) : False := by
  have h1 : CFSG.Open.orderCo1 ∣ Nat.card J := hcard ▸ card_pSimple_dvd J
  have hdvdY : CFSG.Open.orderCo1 ∣ Nat.card Y := by
    have h2 : Nat.card J ∣ Nat.card (S8.cx y) := Subgroup.card_dvd_of_le hJ.1
    have h3 : Nat.card (S8.cx y) ∣ Nat.card Y := Subgroup.card_subgroup_dvd_card _
    exact h1.trans (h2.trans h3)
  have hYs : Nat.card Y = sporOrd s :=
    (Nat.card_congr e.toEquiv).trans (sporadicOrdersTable_holds s)
  have h13 : 13 ∣ Nat.card J := by
    have h13co : (13 : ℕ) ∣ CFSG.Open.orderCo1 := by norm_num [CFSG.Open.orderCo1]
    exact h13co.trans h1
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) 13 h13
  have hw : orderOf (z : Y) = 13 := by rw [Subgroup.orderOf_coe]; exact hz
  have hzC : (z : Y) ∈ S8.cx y := hJ.1 z.2
  have hcomm : Commute y (z : Y) := (Subgroup.mem_centralizer_singleton_iff.1 hzC).symm
  have hcop : Nat.Coprime (orderOf y) (orderOf (z : Y)) := by
    rw [hy, hw]
    norm_num
  have hord : orderOf (y * (z : Y)) = 65 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hy, hw]
  have h65 : orderOf (e (y * (z : Y))) = 65 := by
    rw [MulEquiv.orderOf_eq]
    exact hord
  rcases spor_of_co1_dvd s (hYs ▸ hdvdY) with rfl | rfl | rfl
  · exact I1420.noOrderSixtyFiveAt_Co1 (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Co1)
      (e (y * (z : Y))) h65
  · exact hBM .B (Or.inl rfl) (e (y * (z : Y))) h65
  · exact hBM .M (Or.inr rfl) (e (y * (z : Y))) h65

end Spor

end CFSG.LocalAnalysis.GLTheoremA.No5
