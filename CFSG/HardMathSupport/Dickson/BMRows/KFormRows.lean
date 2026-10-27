module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1ThreeTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporAll
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi24Five
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporCheck
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporCo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporFi23
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporFiveB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporHN
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporHN3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporHe3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporJ3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporLarge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporLy
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporRu3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporSuz
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporTh
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporTh7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporThreeSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporAll
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporCheck
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporCo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporFi23
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporFiveB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporHN
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporHN3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporHe3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporJ3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporLy
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRu3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporSuz
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporTh
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporTh7

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.LocalAnalysis.GLTheoremA CFSG.AGLEmbeddingD2.Wilson CFSG.HardMathSupport.Timmesfeld
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)
open CFSG.HardMathSupport.Timmesfeld.Proving (sporadicOuterLeTwo_holds)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable LieOrderBridge
  sporadicOrdersTable_holds lieOrderBridge_holds)
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporFactors)

section SQ
open CFSG.LocalAnalysis.GLTheoremA.I1416QRows

theorem qrow_of_ne_BM {s : TauCeti.SporadicName} (hsB : s ≠ .B) (hsM : s ≠ .M) (p : ℕ) :
    I1416QRows.I1416QRow s p := by
  have hOut : SporadicOuterLeTwo := sporadicOuterLeTwo_holds
  have hbr : SporadicBridges := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hOrd : SporadicOrdersTable := sporadicOrdersTable_holds
  have hb : LieOrderBridge := lieOrderBridge_holds
  cases s
  case B => exact absurd rfl hsB
  case M => exact absurd rfl hsM
  all_goals refine I1416QRows.qrow_of_factors hOut hbr hOrd hsB hsM (fun x hx h2 he => ?_) p
  all_goals simp only [sporFactors, List.mem_cons, List.not_mem_nil, or_false] at hx
  all_goals rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact absurd rfl h2 | (exfalso; omega) | skip
  case M11 => exact qrow_M11_three hOut
  case M12 => exact qrow_M12_three hOut
  case M22 => exact qrow_M22_three hOut
  case M23 => exact qrow_M23_three hOut hbr
  case M24 => exact qrow_M24_three hOut hbr hb
  case J2.inr.inl => exact qrow_J2_three hOut hbr hb
  case J2.inr.inr.inl => exact qrow_J2_five hOut hbr
  case J3.inr.inl => exact I271.I1416QJ3.qrow_J3_three hOut hbr hb
  case J4.inr.inl => exact NormalizerAction.qrow_J4_three hOut hbr hb
  case J4.inr.inr.inr.inr.inl => exact qrow_J4_eleven hbr hOut
  case HS.inr.inl => exact qrow_HS_three hOut hbr
  case HS.inr.inr.inl => exact qrow_HS_five hOut hbr
  case McL.inr.inl => exact qrow_McL_three hOut hbr
  case McL.inr.inr.inl => exact qrow_McL_five hOut hbr
  case He.inr.inl => exact qrow_He_three hOut hbr hb
  case He.inr.inr.inl => exact qrow_He_five hOut hbr
  case He.inr.inr.inr.inl => exact qrow_He_seven hOut hbr
  case Ru.inr.inl => exact qrow_Ru_three hOut hbr hb
  case Ru.inr.inr.inl => exact qrow_Ru_five hOut hbr
  case Suz.inr.inl => exact I271.I1416QSuz.qrow_Suz_three hOut hbr hb
  case Suz.inr.inr.inl => exact qrow_Suz_five hOut hbr hb
  case ONan.inr.inl => exact qrow_ON_three hOut hbr hb
  case ONan.inr.inr.inr.inl => exact qrow_ON_seven hOut
  case Co1.inr.inl => exact I271.TabCo1.qrow_Co1_three hOut hbr hb
  case Co1.inr.inr.inl => exact I271.TabCo1.qrow_Co1_five hOut hbr hb
  case Co1.inr.inr.inr.inl => exact SporadicBalance.Co1S.qrow_Co1_seven hOut hbr hb
  case Co2.inr.inl => exact I271.I1416QCo2.qrow_Co2_three hOut hbr hb
  case Co2.inr.inr.inl => exact qrow_Co2_five hOut hbr
  case Co3.inr.inl => exact I271.I1416QCo3.qrow_Co3_three hOut hbr hb
  case Co3.inr.inr.inl => exact qrow_Co3_five hOut hbr
  case Fi22.inr.inl => exact I271.I1416QFi22.qrow_Fi22_three hOut hbr hb
  case Fi22.inr.inr.inl => exact qrow_Fi22_five hOut hbr
  case Fi23.inr.inl => exact I271.I1416QFi23.qrow_Fi23_three hOut hbr hb
  case Fi23.inr.inr.inl => exact SporadicBalance.Fi23Five.qrow_Fi23_five hOut hbr hb
  case Fi24Prime.inr.inl => exact I271.TabFi24.qrow_Fi24_three hOut hbr hb
  case Fi24Prime.inr.inr.inl => exact Fi24FiveRows.qrow_Fi24_five hOut hbr hb
  case Fi24Prime.inr.inr.inr.inl => exact I271.Fi7.qrow_Fi24_seven hOut hbr hb
  case HN.inr.inl => exact I271.I1416HN3.qrow_HN_three hOut hbr hb
  case HN.inr.inr.inl => exact I271.I1416HN.qrow_HN_five hOut hbr hb
  case Ly.inr.inl => exact I271.I1416QLy.qrow_Ly_three hOut hbr hb
  case Ly.inr.inr.inl => exact qrow_Ly_five hOut hbr
  case Th.inr.inl => exact I271.I1416QTh.qrow_Th_three hOut hbr hb
  case Th.inr.inr.inl => exact qrow_Th_five hOut hbr
  case Th.inr.inr.inr.inl =>
    exact SporadicBalance.ThSeven.qrow_Th_seven hOut hbr

end SQ

section ST
open CFSG.LocalAnalysis.GLTheoremA.I1416Rows

theorem row_of_ne_BM {s : TauCeti.SporadicName} (hsB : s ≠ .B) (hsM : s ≠ .M) (p : ℕ) :
    I1416Rows.I1416SporRow s p := by
  have hOut : SporadicOuterLeTwo := sporadicOuterLeTwo_holds
  have hbr : SporadicBridges := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hOrd : SporadicOrdersTable := sporadicOrdersTable_holds
  have hb : LieOrderBridge := lieOrderBridge_holds
  cases s
  case B => exact absurd rfl hsB
  case M => exact absurd rfl hsM
  all_goals refine I1416Rows.row_of_factors hOut hbr hOrd hsB hsM (fun x hx h2 he => ?_) p
  all_goals simp only [sporFactors, List.mem_cons, List.not_mem_nil, or_false] at hx
  all_goals rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact absurd rfl h2 | (exfalso; omega) | skip
  case M11 => exact row_M11_three hOut
  case M12 => exact row_M12_three hOut
  case M22 => exact row_M22_three hOut
  case M23 => exact row_M23_three hOut hbr
  case M24 => exact row_M24_three hOut hbr hb
  case J2.inr.inl => exact row_J2_three hOut hbr hb
  case J2.inr.inr.inl => exact row_J2_five hOut hbr
  case J3.inr.inl => exact I271.I1416J3.row_J3_three hOut hbr
  case J4.inr.inl => exact NormalizerAction.row_J4_three hOut hbr hb
  case J4.inr.inr.inr.inr.inl => exact row_J4_eleven hbr hOut
  case HS.inr.inl => exact row_HS_three hOut hbr
  case HS.inr.inr.inl => exact row_HS_five hOut hbr
  case McL.inr.inl => exact row_McL_three hOut hbr
  case McL.inr.inr.inl => exact row_McL_five hOut hbr
  case He.inr.inl => exact row_He_three hOut hbr hb
  case He.inr.inr.inl => exact row_He_five hOut hbr
  case He.inr.inr.inr.inl => exact row_He_seven hOut hbr
  case Ru.inr.inl => exact row_Ru_three hOut hbr hb
  case Ru.inr.inr.inl => exact row_Ru_five hOut hbr
  case Suz.inr.inl => exact I271.I1416Suz.row_Suz_three hOut hbr hb
  case Suz.inr.inr.inl => exact row_Suz_five hOut hbr hb
  case ONan.inr.inl => exact row_ON_three hOut hbr
  case ONan.inr.inr.inr.inl => exact row_ON_seven hOut
  case Co1.inr.inl => exact I271.TabCo1.row_Co1_three hOut hbr hb
  case Co1.inr.inr.inl => exact I271.TabCo1.row_Co1_five hOut hbr hb
  case Co1.inr.inr.inr.inl => exact SporadicBalance.Co1S.row_Co1_seven hOut hbr hb
  case Co2.inr.inl => exact I271.I1416Co2.row_Co2_three hOut hbr
  case Co2.inr.inr.inl => exact row_Co2_five hOut hbr
  case Co3.inr.inl => exact I271.I1416Co3.row_Co3_three hOut hbr
  case Co3.inr.inr.inl => exact row_Co3_five hOut hbr
  case Fi22.inr.inl => exact I271.I1416Fi22.row_Fi22_three hOut hbr hb
  case Fi22.inr.inr.inl => exact row_Fi22_five hOut hbr
  case Fi23.inr.inl => exact I271.I1416Fi23.row_Fi23_three hOut hbr hb
  case Fi23.inr.inr.inl => exact SporadicBalance.Fi23Five.row_Fi23_five hOut hbr hb
  case Fi24Prime.inr.inl => exact I271.TabFi24.row_Fi24_three hOut hbr hb
  case Fi24Prime.inr.inr.inl => exact Fi24FiveRows.row_Fi24_five hOut hbr hb
  case Fi24Prime.inr.inr.inr.inl => exact I271.Fi7.row_Fi24_seven hOut hbr hb
  case HN.inr.inl => exact I271.I1416HN3.row_HN_three hOut hbr hb
  case HN.inr.inr.inl => exact I271.I1416HN.row_HN_five hOut hbr hb
  case Ly.inr.inl => exact I271.I1416Ly.row_Ly_three hOut hbr hb
  case Ly.inr.inr.inl => exact row_Ly_five hOut hbr
  case Th.inr.inl => exact I271.I1416Th.row_Th_three hOut hbr hb
  case Th.inr.inr.inl => exact row_Th_five hOut hbr
  case Th.inr.inr.inr.inl =>
    exact SporadicBalance.ThSeven.row_Th_seven hOut hbr

end ST

section SC
open CFSG.LocalAnalysis.GLTheoremA.Chev2Rows

theorem crow_of_ne_BM {s : TauCeti.SporadicName} (hsB : s ≠ .B) (hsM : s ≠ .M) (p : ℕ) :
    Chev2Rows.CRow s p := by
  have hOut : SporadicOuterLeTwo := sporadicOuterLeTwo_holds
  have hbr : SporadicBridges := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hOrd : SporadicOrdersTable := sporadicOrdersTable_holds
  have hb : LieOrderBridge := lieOrderBridge_holds
  cases s
  case B => exact absurd rfl hsB
  case M => exact absurd rfl hsM
  all_goals refine Chev2Rows.crow_of_factors hOut hbr hOrd hsB hsM (fun x hx h2 he => ?_) p
  all_goals simp only [sporFactors, List.mem_cons, List.not_mem_nil, or_false] at hx
  all_goals rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact absurd rfl h2 | (exfalso; omega) | skip
  case M11 => exact crow_M11_three hOut
  case M12 => exact crow_M12_three hOut
  case M22 => exact crow_M22_three hOut
  case M23 => exact crow_M23_three hOut hbr
  case M24 => exact crow_M24_three hOut hbr hb
  case J2.inr.inl => exact crow_J2_three hOut hbr hb
  case J2.inr.inr.inl => exact crow_J2_five hOut hbr
  case J3.inr.inl => exact I271.Chev2J3.crow_J3_three hOut hbr hb
  case J4.inr.inl => exact NormalizerAction.crow_J4_three hOut hbr hb
  case J4.inr.inr.inr.inr.inl => exact crow_J4_eleven hbr hOut
  case HS.inr.inl => exact crow_HS_three hOut hbr
  case HS.inr.inr.inl => exact crow_HS_five hOut hbr
  case McL.inr.inl => exact crow_McL_three hOut hbr
  case McL.inr.inr.inl => exact crow_McL_five hOut hbr
  case He.inr.inl => exact crow_He_three hOut hbr hb
  case He.inr.inr.inl => exact crow_He_five hOut hbr
  case He.inr.inr.inr.inl => exact crow_He_seven hOut hbr hb
  case Ru.inr.inl => exact crow_Ru_three hOut hbr hb
  case Ru.inr.inr.inl => exact crow_Ru_five hOut hbr
  case Suz.inr.inl => exact I271.Chev2Suz.crow_Suz_three hOut hbr hb
  case Suz.inr.inr.inl => exact crow_Suz_five hOut hbr hb
  case ONan.inr.inl => exact crow_ON_three hOut hbr hb
  case ONan.inr.inr.inr.inl => exact crow_ON_seven hOut
  case Co1.inr.inl => exact I271.TabCo1.crow_Co1_three hOut hbr hb
  case Co1.inr.inr.inl => exact I271.TabCo1.crow_Co1_five hOut hbr hb
  case Co1.inr.inr.inr.inl =>
    exact SporadicBalance.Co1S.crow_Co1_seven hOut hbr hb
  case Co2.inr.inl => exact I271.Chev2Co2.crow_Co2_three hOut hbr hb
  case Co2.inr.inr.inl => exact crow_Co2_five hOut hbr
  case Co3.inr.inl => exact I271.Chev2Co3.crow_Co3_three hOut hbr hb
  case Co3.inr.inr.inl => exact crow_Co3_five hOut hbr
  case Fi22.inr.inl => exact I271.Chev2Fi22.crow_Fi22_three hOut hbr hb
  case Fi22.inr.inr.inl => exact crow_Fi22_five hOut hbr
  case Fi23.inr.inl => exact I271.Chev2Fi23.crow_Fi23_three hOut hbr hb
  case Fi23.inr.inr.inl =>
    exact SporadicBalance.Fi23Five.crow_Fi23_five hOut hbr hb
  case Fi24Prime.inr.inl => exact I271.TabFi24.crow_Fi24_three hOut hbr hb
  case Fi24Prime.inr.inr.inl => exact Fi24FiveRows.crow_Fi24_five hOut hbr hb
  case Fi24Prime.inr.inr.inr.inl => exact I271.Fi7.crow_Fi24_seven hOut hbr hb
  case HN.inr.inl => exact I271.Chev2HN3.crow_HN_three hOut hbr hb
  case HN.inr.inr.inl => exact I271.Chev2HN.crow_HN_five hOut hbr hb
  case Ly.inr.inl => exact I271.Chev2Ly.crow_Ly_three hOut hbr hb
  case Ly.inr.inr.inl => exact crow_Ly_five hOut hbr
  case Th.inr.inl => exact I271.Chev2Th.crow_Th_three hOut hbr hb
  case Th.inr.inr.inl => exact crow_Th_five hOut hbr
  case Th.inr.inr.inr.inl =>
    exact SporadicBalance.ThSeven.crow_Th_seven hOut hbr hb

end SC

end CFSG.HardMathSupport.Dickson.BMRows
