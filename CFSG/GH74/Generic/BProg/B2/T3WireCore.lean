module

public import CFSG.GH74.Generic.BProg.B2.T3WireDefs
public import CFSG.GH74.Generic.BProg.B2.T3Sect13C1
public import CFSG.GH74.Generic.BProg.B2.SDRLeaf

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg Subgroup

namespace T3Wire

variable {G : Type} [Group G] [Finite G] {x : G} {K A M P Q H : Subgroup G}

theorem pRank_CMbar_le_one_c1 (hNo : NoJPrimeNonSD) (hSD : SDR.Stage2SDRankC)
    (hT2 : Stage2Thm2C) (hs : Stage2Setup G x K A M P Q) (h1 : Stage2Concl1 x K M Q H)
    (hc1 : barIn M H = barIn M K) : pRank 2 ↥(CMbar M K) ≤ 1 := by
  by_cases h3 : B1.QShape3SD (↥K ⧸ pPrimeCore 2 ↥K)
  · exact SDR.sdRank_of_core hSD hT2 hs (Stage2Concl1.toCore h1) h3 hc1
  · exact pRank_CMbar_le_one hNo hs h1.K_le h3 h1.H_min hc1

theorem false_of_c1 (hZ : CenterlessS345) (hF3 : InvolFixFour QShape3)
    (hF4 : InvolFixFour QShape4) (hF5 : InvolFixFour QShape5) (hC3 : FourConj QShape3)
    (hC4 : FourConj QShape4) (hC5 : FourConj QShape5) (hNo : NoJPrimeNonSD)
    (hSD : SDR.Stage2SDRankC) (hT2 : Stage2Thm2C) (hS1 : Stage2Thm3S1)
    (hs : Stage2Setup G x K A M P Q) (h1 : Stage2Concl1 x K M Q H) (h2 : Stage2Concl2 M)
    (hc : Stage2Cor2 x K A M H) (hc1 : barIn M H = barIn M K) : False := by
  have hr := pRank_CMbar_le_one_c1 hNo hSD hT2 hs h1 hc1
  obtain ⟨-, -, -, hcase⟩ := hs.src
  rcases hcase with ⟨hAK, hK1⟩ | ⟨_, -, -, -, -, -, hshape⟩
  · exact hS1 G x K A M P Q H hs h1 h2 hc hAK hK1 hc1
      (centralizer_x_le_M_of hZ hs h1.K_le h1.Q_le h2) hr
  · refine false_of_c1_S345_of hZ hF3 hF4 hF5 hC3 hC4 hC5 hs h1.K_le h1.Q_le h2
      (fun hK1 => ?_) h1.H_min hc1 hr
    exact B1.PilotS3.not_qShape1_of_center_trivial hK1
      (hZ _ (TwoThin.isQuasisimple_hat hs.pair.1.1.1.2.2) hshape)

theorem stage2Thm3_of_S1_of (hZ : CenterlessS345) (hF3 : InvolFixFour QShape3)
    (hF4 : InvolFixFour QShape4) (hF5 : InvolFixFour QShape5) (hC3 : FourConj QShape3)
    (hC4 : FourConj QShape4) (hC5 : FourConj QShape5) (hNo : NoJPrimeNonSD)
    (hSD : SDR.Stage2SDRankC) (hT2 : Stage2Thm2C) (hS1 : Stage2Thm3S1) : Stage2Thm3 := by
  intro G _ _ x K A M P Q H hs h1 h2 hc
  refine ⟨hc.e.resolve_left fun hc1 => ?_, centralizer_x_le_M_of hZ hs h1.K_le h1.Q_le h2⟩
  exact false_of_c1 hZ hF3 hF4 hF5 hC3 hC4 hC5 hNo hSD hT2 hS1 hs h1 h2 hc hc1

end T3Wire

end CFSG.GH74.Generic.BProg.B2
