module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YWire
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63Top
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AZ
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A3Fin
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B8h
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAN24Main
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C78
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79z
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CLie
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Holds
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2PslMain
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2PsuMain
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2OmMain
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2OutMain
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.Final
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LBridge
public import CFSG.LocalAnalysis.EvenBN.GMSK.LayerListK
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.CTEvenResidualMilestone
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.OddSporadicHolds
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldG2Eight
public import CFSG.Milestones.ASVolI.I3Components

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

theorem yamadaCase3Core_holds :
    CFSG.OddStandard.HigherRank.G2Three.YamadaCase3Core :=
  yamadaCase3Core_wire CFSG.OddStandard.HigherRank.G2Three.g23Facts_holds
    (CFSG.OddStandard.HigherRank.G2Three.Sec2.y2l_sec62' sec3Inputs_of)
    (sec63'_of_certs sec3Inputs_of)
    (sec64b'_of sec3Inputs_of
      (y6Four4a_holds sec3Inputs_of CFSG.OddStandard.HigherRank.G2Three.g23Facts_holds
        CFSG.LocalAnalysis.EvenBN.GMSK.gmsLinearStandardLayerListKRankOne
        CFSG.EvenSporadicStandard.Induction.ctEvenResidualStatement_of_milestone
        CFSG.RankThree.PartOne.SPOR.schreierFor_catalog
        CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
        CFSG.ComponentClassification.CatFC.card_carrier_eq_sporOrder_all
        (fun k _ _ hk =>
          (CFSG.HardMathSupport.Timmesfeld.CrossChar.simple_card_commutator_adjointG2_two k
            hk).2)))
    (sec7A_holds sec3Inputs_of) (sec7B_holds sec3Inputs_of)
    (sec7C_of
        (sec77_holds sec3Inputs_of CFSG.ASVolI.as_I_3_1 nar24_holds
            (y7c_hopf_gl3_dvd_two l2Griess_holds))
        (sec78_holds sec3Inputs_of CFSG.ASVolI.as_I_3_1 nar24_holds
            (y7c_hopf_gl3_dvd_two l2Griess_holds))
        (sec79_holds sec3Inputs_of (y7c_hopf_gl3_dvd_two l2Griess_holds)))
    (CFSG.OddStandard.HigherRank.G2Three.Sec2.y2l_sec7NT sec3Inputs_of)
    (gomi1RKP_of_literature (gomiOuterPSLU4_of_table l2Griess_holds)
        (l2NoPauliPSL_of_table l2Griess_holds) (l2NoPauliPSU_of_table l2Griess_holds)
        (l2NoPauliPOmega_of_table l2Griess_holds))

end CFSG.OddStandard.HigherRank.YamadaG23
