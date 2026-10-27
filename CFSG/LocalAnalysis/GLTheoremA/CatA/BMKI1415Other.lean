module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporAll
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporHN3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporCo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporFi23
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporFive
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporHN
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporLarge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporLy
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporSuz
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporTh
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporTh7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1ThreeRows

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1415Rows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporFactors)

section BMKOther


theorem i1415Row_of_ne_BM
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    {s : TauCeti.SporadicName} (hsB : s ≠ .B) (hsM : s ≠ .M) (p : ℕ) : I1415Row s p := by
  cases s
  case B => exact absurd rfl hsB
  case M => exact absurd rfl hsM
  all_goals refine arow_of_factors hOut hbr hOrd (by decide) (by decide) (fun x hx h2 he hd => ?_) p
  all_goals simp only [sporFactors, List.mem_cons, List.not_mem_nil, or_false] at hx
  all_goals rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd rfl h2
    | (exfalso; omega)
    | (exfalso; revert hd
       norm_num [CFSG.HardMathSupport.Solomon.Coordinator.sporOrd, CFSG.Open.orderJ3,
        CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1,
        CFSG.Open.orderFi23, CFSG.Open.orderFi24Prime, CFSG.Open.orderHN, CFSG.Open.orderLy,
        CFSG.Open.orderTh]; done)
    | skip
  case McL.inr.inl => exact arow_McL_three hOut hbr
  case McL.inr.inr.inl => exact arow_McL_five hOut hbr
  case Suz.inr.inl => exact CFSG.HardMathSupport.Dickson.I271.I1415ASuz.arow_Suz_three hOut hbr hb
  case Ly.inr.inl => exact CFSG.HardMathSupport.Dickson.I271.I1415ALy.arow_Ly_three hOut hbr hb
  case Ly.inr.inr.inl => exact arow_Ly_five hOut hbr
  case Th.inr.inl => exact CFSG.HardMathSupport.Dickson.I271.I1415ATh.arow_Th_three hOut hbr hb
  case Th.inr.inr.inl => exact arow_Th_five hOut hbr
  case Th.inr.inr.inr.inl =>
    exact CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSeven.arow_Th_seven hOut hbr
  case HN.inr.inl =>
    exact CFSG.HardMathSupport.Dickson.I271.I1415AHN3.arow_HN_three hOut hbr hb
  case HN.inr.inr.inl => exact CFSG.HardMathSupport.Dickson.I271.I1415AHN.arow_HN_five hOut hbr hb
  case Co1.inr.inl => exact CFSG.HardMathSupport.Dickson.I271.TabCo1.arow_Co1_three hOut hbr
  case Co1.inr.inr.inl => exact CFSG.HardMathSupport.Dickson.I271.TabCo1.arow_Co1_five hOut hbr
  case Co1.inr.inr.inr.inl =>
    exact CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S.arow_Co1_seven hOut hbr
  case Co2.inr.inl => exact CFSG.HardMathSupport.Dickson.I271.I1415ACo2.arow_Co2_three hOut hbr hb
  case Co2.inr.inr.inl => exact arow_Co2_five hOut hbr
  case Co3.inr.inl => exact CFSG.HardMathSupport.Dickson.I271.I1415ACo3.arow_Co3_three hOut hbr hb
  case Co3.inr.inr.inl => exact arow_Co3_five hOut hbr
  case Fi22.inr.inl => exact CFSG.HardMathSupport.Dickson.I271.I1415AFi22.arow_Fi22_three hOut hbr hb
  case Fi23.inr.inl => exact CFSG.HardMathSupport.Dickson.I271.I1415AFi23.arow_Fi23_three hOut hbr hb
  case Fi24Prime.inr.inl =>
    exact CFSG.HardMathSupport.Dickson.I271.TabFi24.arow_Fi24_three hOut hbr
  case Fi24Prime.inr.inr.inr.inl =>
    exact CFSG.HardMathSupport.Dickson.I271.Fi7.arow_Fi24_seven hOut hbr

end BMKOther

end CFSG.LocalAnalysis.GLTheoremA.I1415Rows
