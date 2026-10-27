module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1Out
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2CoreBN1
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43BComp
import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Abstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PointConfig
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIICommon
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.Aut
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionCyclic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionShadow
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup

variable {Y : Type} [Group Y] [Finite Y] {Pb : Subgroup Y} {a c y : Y} {L₁ L₂ : Subgroup Y} {t : Y}

theorem sz32b_isSylowOf_N1 (hY : Sz32Case2Data Pb a c y) (h : Szh1Two Pb L₁ L₂ t) :
    CFSG.ABGLocalTools.IsSylowOf 5 Pb (Subgroup.normalizer (L₁ : Set Y)) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨S, hS⟩ := hY.sylow
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨sz32b_Pb_le_N1 h, ?_, ?_⟩
  · rw [← hS]
    exact S.isPGroup'
  · intro hd
    apply S.not_dvd_index
    rw [hS]
    exact hd.trans (Subgroup.relIndex_dvd_index_of_le (sz32b_Pb_le_N1 h))

theorem sz32b_pRank_le_one (hY : Sz32Case2Data Pb a c y) (h : Szh1Two Pb L₁ L₂ t)
    (hs : Szh1Cyc Pb a c y L₁ L₂) :
    CFSG.Open.pRank 5 (⊤ : Subgroup ↥L₁) ≤ 1 ∧ CFSG.Open.pRank 5 (⊤ : Subgroup ↥L₂) ≤ 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hP := sz32b_isSylowOf_N1 hY h
  have hL1 : CFSG.ABGLocalTools.IsSylowOf 5 (Pb ⊓ L₁) L₁ :=
    hP.inf_of_le_normalizer (sup_le_iff.1 (sz32b_sup_le_N1 h)).1 le_rfl
  have hL2 : CFSG.ABGLocalTools.IsSylowOf 5 (Pb ⊓ L₂) L₂ :=
    hP.inf_of_le_normalizer (sup_le_iff.1 (sz32b_sup_le_N1 h)).2
      (fun g hg => sz32b_N1_mem_N2 h hg)
  obtain ⟨Q₁, hQ₁⟩ := hL1.exists_sylow_eq_subgroupOf
  obtain ⟨Q₂, hQ₂⟩ := hL2.exists_sylow_eq_subgroupOf
  refine ⟨szh1_pRank_le_one_of_cyclic_sylow Q₁ ?_, szh1_pRank_le_one_of_cyclic_sylow Q₂ ?_⟩
  · obtain ⟨g, -, hg⟩ := hs.cyc₁
    rw [hQ₁]
    have hc : IsCyclic ↥(Pb ⊓ L₁) := by rw [hg]; infer_instance
    exact (Subgroup.subgroupOfEquivOfLe inf_le_right).isCyclic.2 hc
  · obtain ⟨g, -, hg⟩ := hs.cyc₂
    rw [hQ₂]
    have hc : IsCyclic ↥(Pb ⊓ L₂) := by rw [hg]; infer_instance
    exact (Subgroup.subgroupOfEquivOfLe inf_le_right).isCyclic.2 hc

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
