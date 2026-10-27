module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatSporBasic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35SporDataA
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35SporDataB
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35SporX
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutMain
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutK3Main

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.Spor

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem noFive_of_card_quotient_center {Y : Type} [Group Y] {c : ℕ} (hc : c ≠ 60)
    (h : Nat.card (Y ⧸ center Y) = c) : NoFive Y := by
  refine ⟨fun e => hc ?_⟩
  have hZ : center Y = ⊥ := Even.center_eq_bot_of_equiv_alt_five e
  rw [← h, hZ, Nat.card_congr (QuotientGroup.quotientBot : Y ⧸ (⊥ : Subgroup Y) ≃* Y).toEquiv]
  exact Even.card_alt_five e

theorem fiveSpor_M11 :
    FiveSporClauseFor .M11 :=
  fiveSpor_of_sporCompData HarrisLit.sporCompData_M11

theorem fiveSpor_M22 :
    FiveSporClauseFor .M22 :=
  fiveSpor_of_sporCompData HarrisLit.sporCompData_M22

theorem fiveSpor_M23 :
    FiveSporClauseFor .M23 :=
  fiveSpor_of_sporCompData HarrisLit.sporCompData_M23

theorem fiveSpor_M24 :
    FiveSporClauseFor .M24 :=
  fiveSpor_of_sporCompData HarrisLit.sporCompData_M24

theorem fiveSpor_Ru :
    FiveSporClauseFor .Ru :=
  fiveSpor_of_sporCompData HarrisLit.sporCompData_Ru

theorem fiveSpor_McL :
    FiveSporClauseFor .McL :=
  fiveSpor_of_sporCompData HarrisLit.sporCompData_McL

theorem fiveSpor_Co2 :
    FiveSporClauseFor .Co2 :=
  fiveSpor_of_sporCompData HarrisLit.sporCompData_Co2

theorem fiveSpor_Co3 :
    FiveSporClauseFor .Co3 :=
  fiveSpor_of_sporCompData HarrisLit.sporCompData_Co3

theorem fiveSpor_Th :
    FiveSporClauseFor .Th :=
  fiveSpor_of_sporCompData HarrisLit.sporCompData_Th

theorem fiveSpor_Fi23 :
    FiveSporClauseFor .Fi23 :=
  fiveSpor_of_sporCompData HarrisLit.sporCompData_Fi23

theorem fiveSpor_B :
    FiveSporClauseFor .B :=
  fiveSpor_of_sporCompData HarrisLit.sporCompData_B

theorem fiveSpor_Co1 :
    FiveSporClauseFor .Co1 :=
  fiveSpor_of_sporCompData HarrisLit.sporCompData_Co1

theorem fiveSpor_Fi22 :
    FiveSporClauseFor .Fi22 :=
  fiveSpor_of_sporCompData HarrisLit.sporCompData_Fi22

theorem fiveSpor_Fi24Prime :
    FiveSporClauseFor .Fi24Prime :=
  fiveSpor_of_sporCompData HarrisLit.sporCompData_Fi24Prime

theorem fiveSpor_Ly :
    FiveSporClauseFor .Ly :=
  fiveSpor_of_sporCompData HarrisLit.sporCompData_Ly

theorem fiveSpor_J4 :
    FiveSporClauseFor .J4 :=
  fiveSpor_of_sporCompData HarrisLit.sporCompData_J4

theorem fiveSpor_HN :
    FiveSporClauseFor .HN :=
  fiveSpor_of_sporCompData HarrisLit.sporCompData_HN

theorem fiveSpor_M
    :
    FiveSporClauseFor .M :=
  fiveSpor_of_sporCompData HarrisLit.sporCompData_M

theorem fiveSpor_Suz :
    FiveSporClauseFor .Suz :=
  fiveSpor_of_comps CatalogueU.sporadicOddCoreFree_Suz
    (fun _ _ _ _ _ ⟨e⟩ t ht B hB => noFive_of_card_quotient_center (c := 20160) (by norm_num)
      (Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order e t ht B hB))
    (fun G _ _ _ _ hG α hα2 hα B hB => by
      rcases suzOuterComponentsInput_holds G hG α hα2 hα B hB with h | h
      · exact noFive_of_card_quotient_center (c := 95040) (by norm_num) h
      · exact noFive_of_card_quotient_center (c := 604800) (by norm_num) h)

theorem fiveSpor_ONan :
    FiveSporClauseFor .ONan :=
  fiveSpor_of_comps Sporadic.ONOddCore.sporadicOddCoreFree_ONan
    (fun _ _ _ _ _ hG t ht B hB => noFive_of_card_quotient_center (c := 20160) (by norm_num)
      (Sporadic.ONOddCore.cti_on_involution_local_components_projective_linear_quotient_order hG
        t ht B hB))
    (fun G _ _ _ _ hG α hα2 hα B hB => noFive_of_card_quotient_center (c := 175560)
      (by norm_num)
      (onOuterComponentsInput_of_local ONOut.onOuterLocalInput_holds G hG α hα2 hα B hB))

end CFSG.ComponentClassification.SolMax.FiveCat.Spor
