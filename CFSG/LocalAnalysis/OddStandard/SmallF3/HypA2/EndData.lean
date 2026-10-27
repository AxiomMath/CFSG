module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.EndDataDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.ResidualILo
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.ResidualInS
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Terminal
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.RankOne
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LemmaT
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LemmaD
public import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint

theorem exists_endData (hI : Phase1Inputs) (hA7 : TwoA7RankOne) (hP : Phase2Inputs)
    (hL : Leaves2) {G : Type} [Group G] [Finite G] (hG : HSetting G) {y : G}
    (hy : orderOf y = 2) {K : Subgroup G}
    (hK : Omega.IsComponentIn K (centralizer ({y} : Set G))) (hres : IsResidualA2 ↥K) :
    ∃ (x : G) (Y : Subgroup G), EndData G x Y := by
  haveI := hG.simple
  obtain ⟨hIL, h3⟩ := isILo_of_residual hL.residualRank hG.balanced hy hK hres
  have hKS : InS (↥K ⧸ center ↥K) :=
    inS_of_isResidualA2 hL.residualNotChevOdd hP.a8 hP.orders hP.g2Four hres
  obtain ⟨x, Y, hterm, hYS⟩ := exists_twoTerminal_inS hL.closure hP.bIg hG h3 hIL hKS
  have hT : GH74.GLS.IsTerminalPair 2 x Y :=
    isTerminalPair_of_isTwoTerminal hG.balanced (fun t ht => hG.rank_centralizer h3 ht) hterm
  have hILo : GH74.GLS.IsILo 2 x Y := hterm.1
  have hx : orderOf x = 2 := hILo.1
  have hYle : Y ≤ centralizer ({x} : Set G) := hILo.2.2.1
  have hY2 : IsPComponent 2 (Y.subgroupOf (centralizer ({x} : Set G))) := hILo.2.2.2
  have hcomp : Omega.IsComponentIn Y (centralizer ({x} : Set G)) :=
    isComponentIn_of_isPComponent (hG.balanced x hx) hYle hY2
  by_cases hr : 2 ≤ CFSG.pRank 2 ↥Y
  ·
    have hstd : CFSG.IsStandardSubgroup Y :=
      hP.bPU4 G hG.isKProperSimple x Y hx hILo.2.2 hr hT
    exact ⟨x, Y, ⟨hG, hx, hcomp,
      CFSG.IsStandardSubgroup.standardComponentIsStandard hstd, hYS⟩⟩
  ·
    have hrle : CFSG.pRank 2 ↥Y ≤ 1 := by have hlt := not_le.mp hr; omega
    have hQuasi : IsQuasisimple ↥Y :=
      CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hYle).symm hcomp.2.1
    have hO : oddCore ↥Y = ⊥ := oddCore_eq_bot_of_isComponentIn (hG.balanced x hx) hcomp
    have hbig : 20160 ≤ Nat.card (↥Y ⧸ center ↥Y) := twentyThousand_le_card_of_inS hYS
    have hdat : CentralDatum ↥Y :=
      centralDatum_of_pRank_le_one hI.griess hP.dihedral hQuasi hO hbig hrle
    exact (false_of_centralDatum hI hA7 G hG.nonab hG.kProper hG.notCat x Y hx hcomp hdat).elim

end CFSG.OddStandard.SmallF3.HypA2
