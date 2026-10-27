module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobFi22Setting
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.TBLitPropC
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.PerfectCentralQuotientOuter
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSchreier
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Mult
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Dichotomy
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Input
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobBalance
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobFactor
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobFi22Square
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSetting
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterRowFusion
public import CFSG.LocalAnalysis.OddStandard.SmallF3Interfaces
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import CFSG.RankThree.Classical2.UnitarySplitPrimeRank
public import CFSG.RankThree.Coprime.EvenCenterSectionCover
public import CFSG.RankThree.Native.Fi22UTwoRank
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.Walter.JRFacts
public import Certificates.Certificate3085Base

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Schreier CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore
open CFSG.EvenSporadicStandard.HypOne.Fi22

section Model


theorem fi22_model {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G}
    (hL : IsSporadic L .Fi22) (hu : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L)
    (hKu : ∀ k ∈ K, k * u = u * k) (hcard : 18393661440 ≤ Nat.card K) :
    K = L ⊓ centralizer ({u} : Set G) ∧ CentralizerModel ↥L (⟨u, hu⟩ : ↥L) := by
  have hKeq := fi22_eq_inf_centralizer hL hu hu2 hKL hKu hcard
  obtain ⟨hq, hZ⟩ := fi22_quasisimple_center hL hu hu2 hKL hKu hcard
  obtain ⟨Φ, hΦ, hK⟩ := exists_equiv_fi22 hL hu hu2 hKL hKu hcard
  have hzH : (⟨u, hu⟩ : ↥L) ∈ K.subgroupOf L :=
    mem_subgroupOf.2 (by rw [hKeq]; exact ⟨hu, mem_centralizer_singleton_iff.2 rfl⟩)
  have hKc := subgroupOf_eq_centralizer hu hKeq
  set t₂ : ↥fi22P := ⟨fi22ExtRep 2, fi22ExtRep_two_mem⟩ with ht₂
  have hu' : Φ.symm t₂ = (⟨u, hu⟩ : ↥L) := by
    rw [← hΦ]
    exact Φ.symm_apply_apply _
  have hc : centralizer ({(⟨u, hu⟩ : ↥L)} : Set ↥L) =
      (centralizer ({t₂} : Set ↥fi22P)).map Φ.symm.toMonoidHom := by
    rw [← hu']
    exact centralizer_singleton_map_mulEquiv Φ.symm t₂
  refine ⟨hKeq, ?_, ?_, ?_, ?_, ?_, fi22_outTwo_of_isSporadic hL⟩
  · obtain ⟨S, d, hSq⟩ := fi22_squareFacts_P
    refine ⟨S.map Φ.symm.toMonoidHom, Φ.symm d, ?_⟩
    have h1 : SquareFacts ((centralizer ({t₂} : Set ↥fi22P)).map Φ.symm.toMonoidHom)
        (S.map Φ.symm.toMonoidHom) (Φ.symm.toMonoidHom t₂) (Φ.symm.toMonoidHom d) :=
      hSq.map Φ.symm.toMonoidHom Φ.symm.injective
    rw [← hc] at h1
    have h3 : Φ.symm.toMonoidHom t₂ = (⟨u, hu⟩ : ↥L) := hu'
    rwa [h3] at h1
  · rw [hc]
    exact (Φ.symm.mapSubgroup.isCoatom_iff _).2 isCoatom_fi22_centralizer
  · rw [hc]
    have h1 := fi22_centralizer_twoAdic_lt
    have h2 : Nat.card ↥L = Nat.card ↥fi22P := Nat.card_congr Φ.toEquiv
    unfold twoAdic
    rw [Subgroup.card_map_of_injective (f := Φ.symm.toMonoidHom) Φ.symm.injective,
      Subgroup.card_top, h2]
    exact h1
  · rw [← hKc]
    exact (solStd_of_standardComponentIsStandard
      (standard_subgroupOf_centralizer hu hu2 hKeq hq hZ.le)).stdBare
  · rw [← hKc]
    exact card_centralizer_le_of_center hKc hzH hZ.le

theorem fi22_cover_model {Y : Type} [Group Y] [Finite Y] (hY : IsSporadic Y .Fi22) {uY : Y}
    (hu2 : orderOf uY = 2) {KY : Subgroup Y} (hKu : ∀ k ∈ KY, k * uY = uY * k)
    (hcard : 18393661440 ≤ Nat.card KY) :
    KY = centralizer ({uY} : Set Y) ∧ CentralizerModel Y uY := by
  obtain ⟨e⟩ := hY
  have hL : IsSporadic ↥(⊤ : Subgroup Y) .Fi22 := ⟨Subgroup.topEquiv.trans e⟩
  have hu : uY ∈ (⊤ : Subgroup Y) := Subgroup.mem_top _
  obtain ⟨hKeq, hmodel⟩ := fi22_model hL hu hu2 le_top hKu hcard
  refine ⟨by rw [hKeq]; exact top_inf_eq _, ?_⟩
  exact CentralizerModel.of_mulEquiv Subgroup.topEquiv hmodel

end Model

end CFSG.EvenSporadicStandard.Induction
