module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420MainA
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporCardRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMTypeM3
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Co1RowB
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420SuzRow
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420SuzRowFi22
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420SuzCo1Table
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420KDCentre
import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429Inner
import CFSG.LocalAnalysis.GLTheoremA.S3.KD65Holds
import CFSG.HardMathSupport.Solomon.Coordinator.SporOrders
import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo
import CFSG.LocalAnalysis.GLTheoremA.CatC.LieComp3
import CFSG.LocalAnalysis.GLTheoremA.CatC.LieCompHolds
import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDown
import CFSG.Sporadic.Bridge.Catalogue
import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeALocalBase
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeL1Orb
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMDownMGmat
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporBMInvB
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporBMInvM
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMTypeB3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZMathHS5
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Main
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434O8pE9Local
public import Certificates.Certificate17579
public import Certificates.Certificate17580
public import Certificates.Certificate17581
public import Certificates.Data.U62Rank.Check

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.HardMathSupport.Solomon.Coordinator (sporadicOrdersTable_holds lieOrderBridge_holds)
open CFSG.LocalAnalysis.GLTheoremA (kdChevDownQ_three_of_lieComp lieComp_holds kdAltDown_holds
  h1429_kdChevInner_three kd65_holds kdOutChevCentre_holds)
open CFSG.LocalAnalysis.GLTheoremA.K14Spor (cardRow_co3' cardRow_ly' cardRow_th' cardRow_fi23'
  cardRow_fi24')


private theorem i1420Suz_both
    : I1420SuzA ∧ I1420SuzhA := by
  have hOrd := sporadicOrdersTable_holds
  have hOut := CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  have hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges :=
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers :=
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
  have hD : ∀ q : ℕ, KDChevDownQ 3 q := fun q => kdChevDownQ_three_of_lieComp lieComp_holds q
  have h65 : KD65 3 := kd65_holds Nat.prime_three (by norm_num)
  have hCo3 := cardRow_co3' hOut hbr (n := 3265920) (by decide +kernel)
  have hLy := cardRow_ly' hOut hbr (n := 3265920) (by decide +kernel)
  have hTh := cardRow_th' hOut hbr (n := 3265920) (by decide +kernel)
  have hFi23 := cardRow_fi23' hOut hbr (n := 3265920) (by decide +kernel)
  have hFi24 := cardRow_fi24' hbr hOut (n := 3265920) (by decide +kernel) (by decide +kernel)
  have hB := cardRow_B_of_seven_dvd hOut (n := 3265920) (by decide +kernel) (by decide +kernel)
  have hMon := BMType.typeRow3_M typeHyp3_u43 23 (by norm_num) (by norm_num) (by norm_num)
    19 (by norm_num) (by norm_num) (by norm_num)
  have hFi22 := centRow_fi22 hOut hbr
  have hCo1 := centRow_co1 hOut hbr
  exact ⟨i1420SuzA_of_facts kdAltDown_holds lieOrderBridge_holds hD h1429_kdChevInner_three h65
      kdOutChevCentre_holds hOrd hOut hSpM hCo3 hLy hTh hFi23 hFi24 hB hMon hFi22 hCo1,
    i1420SuzhA_of_facts kdAltDown_holds lieOrderBridge_holds hD h1429_kdChevInner_three h65
      kdOutChevCentre_holds hOrd hOut hSpM hCo3 hLy hTh hFi23 hFi24 hB hMon hFi22 hCo1⟩

theorem i1420SuzA_holds
    : I1420SuzA := i1420Suz_both.1

theorem i1420SuzhA_holds
    : I1420SuzhA := i1420Suz_both.2

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
