module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420LyMain
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420LyLie
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420LyAlt
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420LySpor
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420LyHyp
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420LyCo3
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420LyCo1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMTypeB3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMTypeM3

import CFSG.HardMathSupport.Solomon.Coordinator.SporOrders
import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo
import CFSG.LocalAnalysis.GLTheoremA.CatC.LieComp3
import CFSG.LocalAnalysis.GLTheoremA.CatC.LieCompHolds
import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDown
import CFSG.Sporadic.Bridge.Catalogue
import CFSG.Sporadic.McL
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs1415b
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeALocalBase
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeL1Orb
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMDownMGmat
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporBMInvB
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporBMInvM
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZMathHS5
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Main
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434O8pE9Local
public import Certificates.Data.U62Rank.Check

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.BMType
open CFSG.HardMathSupport.Solomon.Coordinator (sporOrd)


theorem i1420LyA_holds : I1420LyA := by
  have hOrd := CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
  have hb := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
  have hOut := CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  have hbr := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hD : ∀ q : ℕ, KDChevDownQ 3 q := fun q =>
    kdChevDownQ_three_of_lieComp lieComp_holds q
  have hF : ∀ m : ℕ, m.factorial / 2 ≠ sporOrd .McL := fun m =>
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1415b.factorial_half_ne_sporOrd m .McL
  have hsimple : IsSimpleGroup (TauCeti.CFSGIndex.sporadic .McL).Group :=
    (MulEquiv.isSimpleGroup_congr (hbr .McL).some).1 CFSG.Sporadic.McL.fam_mcl_simplicity.2.2
  have hP := typeHyp3_mcl hOrd hOut hsimple
  have hrow : ∀ t : TauCeti.SporadicName, (t = .Co3 ∨ t = .Co1 ∨ t = .B ∨ t = .M) →
      TypeRow (S8.sporIs .McL) t := by
    rintro t (rfl | rfl | rfl | rfl)
    · exact typeRow_mcl_of_cardRow hOrd (cardRow_mcl_co3 hOut hbr hb hF)
    · exact typeRow_mcl_of_cardRow hOrd (cardRow_mcl_co1 hOut hbr)
    · exact typeRow3_B hP 13 (by norm_num) (by norm_num) (by norm_num)
    · exact typeRow3_M hP 13 (by norm_num) (by norm_num) (by norm_num) 13 (by norm_num)
        (by norm_num) (by norm_num)
  refine i1420LyA_of_branches
    (fun S _ _ idx e β J h => i1420LieSpor_holds hOrd hD
      (fun q hq T _ _ hT => not_isChevSimple_of_card_mcl hb hT hq) idx e h)
    (fun S _ _ n hn e β J h => i1420AltSpor_holds Nat.prime_three (by norm_num) hOrd
      kdAltDown_holds hF hn e h)
    (fun S _ _ t e β J h => i1420SporLy_holds hOrd hOut hrow e h)

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
