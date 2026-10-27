module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTStmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrIdx
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrImg
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55R3
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.IVK.Lifted.GroupAux
public import CFSG.GH74.GLS.IVK.Lifted.IIAutB
public import CFSG.GH74.GLS.IVK.Lifted.Outer14
public import CFSG.GH74.GLS.IVK.Lifted.SolvAut
public import CFSG.GH74.GLS.IVK.Lifted.Strong
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage1.Main.BrFusedBase
public import CFSG.GH74.GLS.Stage1.Main.BrG2Base
public import CFSG.GH74.GLS.Stage1.Main.BrIndex
public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassA
public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassI
public import CFSG.GH74.GLS.Stage1.Main.II4Proof
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.L284
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Glue2
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Lem47c
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.LeafC1
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx64
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic25
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Statements
public import CFSG.GH74.GLS.Stage2.Local.P27.FullFBuild
public import CFSG.GH74.GLS.Stage2.Local.P27.L4LayerA
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34Perf
public import CFSG.GH74.GLS.Stage2.Local.P34S5SE
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4Merge
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrGH
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrLiftB
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55FitCent
public import CFSG.GH74.GLS.Stage2.Signalizer.L52One
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoI1
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop41
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop43
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop47
public import CFSG.GH74.GLS.TwoThin.KGroupCore
public import CFSG.GH74.Generic.S3.B2Tab1
public import CFSG.GH74.KGroups.L3EpsInvLin
public import CFSG.GH74.Uniqueness.SU.SU13TA1Class
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58Section
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubBasic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCentral
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Transfer
public import CFSG.LocalAnalysis.LargeEvenClassification.Delta
public import CFSG.LocalAnalysis.LargeEvenClassification.NormalCoreIntersection
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreAbsorption
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.JOneRoute
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.NonSquare
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.Remaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.WalterRoute
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.TheoremC
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverBase
public import CFSG.Permutation.BurnsideSchur
public import CFSG.RankThree.PartOne.S10.PlaneContract
public import CFSG.Sporadic.Th.Max3.Packet
public import CFSG.Sporadic.Th.Simple
public import CFSG.Sporadic.ThSchreier.AutCore

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

theorem frameB_of_data {G : Type} [Group G] [Finite G] {k : Kind} {p : ℕ} {H P : Subgroup G}
    {g : G} (hp : p.Prime) (hp2 : p ≠ 2) (hgH : g ∈ H) (hgP : g ∈ P) (hPp : IsPGroup p ↥P)
    {Γ₀ : Type} [Group Γ₀] [Finite Γ₀] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (ρ₀ : Γ₀ →* (V →ₗ[ZMod p] V)ˣ) (hρ : Function.Injective ρ₀)
    (hOp : ∀ N : Subgroup Γ₀, N.Normal → IsPGroup p ↥N → N = ⊥)
    (π : ↥H →* Γ₀) (hπ : Function.Surjective π) {K : Subgroup Γ₀} (hK : IsComponent K)
    (hna : π ⟨g, hgH⟩ ∉ centralizer (K : Set Γ₀))
    (hquad : (((ρ₀ (π ⟨g, hgH⟩) : (V →ₗ[ZMod p] V)ˣ) : V →ₗ[ZMod p] V) - 1) ^ 2 = 0)
    (hgh : GHList (↥K ⧸ center ↥K)) (hr3 : InvSecGroup k (↥K ⧸ center ↥K))
    (hidx : (normalizer (K : Set Γ₀)).index ≤ 2) {J : Subgroup (HBar H)} (hJ : IsComponent J)
    (hJg : ¬ barIn H (zpowers g) ≤ centralizer (J : Set (HBar H))) {Dl : Subgroup ↥H}
    (hDlperf : ⁅Dl, Dl⁆ = Dl) (hDlJ : Dl.map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) = J)
    (hDlK : Dl.map π = K)
    (hDln : ∀ h : ↥H, QuotientGroup.mk' (pPrimeCore 2 ↥H) h ∈ normalizer (J : Set (HBar H)) →
      h ∈ normalizer (Dl : Set ↥H)) :
    BridgeB k p H P g J := by
  have hpf : Fact p.Prime := ⟨hp⟩
  have hO : pCore p Γ₀ = ⊥ := hOp _ pCore_normal pCore_isPGroup
  set N : Subgroup Γ₀ := normalizer (K : Set Γ₀) with hN
  have hNn : N.Normal := normal_of_index_le_two hidx
  have hKN' : K ≤ N := Subgroup.le_normalizer
  set P₁ : Subgroup Γ₀ := (P.subgroupOf H).map π with hP₁
  have hP₁p : IsPGroup p ↥P₁ := map_isPGroup π hPp
  have hP₁N : P₁ ≤ N := by
    intro x hx
    obtain ⟨n, hn⟩ := hP₁p ⟨x, hx⟩
    exact mem_of_pow_prime_pow hp hp2 N hidx (k := n) (congrArg Subtype.val hn)
  have hgP₁ : π ⟨g, hgH⟩ ∈ P₁ := ⟨⟨g, hgH⟩, hgP, rfl⟩
  have haN : π ⟨g, hgH⟩ ∈ N := hP₁N hgP₁
  let a' : ↥N := ⟨π ⟨g, hgH⟩, haN⟩
  have hKc : IsComponent (K.subgroupOf N) := LocalCores.component_overgroup hK hKN'
  obtain ⟨e⟩ := centralQuot_equiv hKN'
  refine ⟨↥N, inferInstance, inferInstance, V, inferInstance, inferInstance, inferInstance,
    ρ₀.comp N.subtype, K.subgroupOf N, a', P₁.subgroupOf N, ?_,
    InvSecGroup.of_equiv e.symm hr3, ?_⟩
  · refine ⟨hp, hp2, hρ.comp N.subtype_injective, ?_, hKc.1, GHList.of_mulEquiv e.symm hgh,
      hquad, ?_, isPGroup_subgroupOf hP₁p N, hgP₁, ?_⟩
    · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKN').mpr le_rfl
    · intro hbot
      apply hna
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 : ⁅(⟨x, hKN' hx⟩ : ↥N), a'⁆ ∈ ⁅K.subgroupOf N, zpowers a'⁆ :=
        Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers a')
      rw [hbot, Subgroup.mem_bot] at h1
      have h3 : (⟨x, hKN' hx⟩ : ↥N) * a' = a' * ⟨x, hKN' hx⟩ :=
        commutatorElement_eq_one_iff_mul_comm.mp h1
      exact congrArg Subtype.val h3
    · intro N' hN'n hN'p
      exact eq_bot_of_normal_pgroup hO N N' hN'n hN'p
  · have hsub : (Dl.map H.subtype).subgroupOf H = Dl :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective Dl
    refine ⟨Γ₀, inferInstance, inferInstance, π, N.subtype, hgH, N.subtype_injective, hπ, ?_,
      ?_, ?_, rfl, ?_, hJ, hJg, Dl.map H.subtype, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Subgroup.range_subtype]
      exact hNn
    · rw [Subgroup.range_subtype]
      exact hidx
    · intro x hx
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hKN'] at hx
      rw [Subgroup.range_subtype]
      exact hx
    · rw [Subgroup.subgroupOf_map_subtype]
      exact inf_of_le_left hP₁N
    · rintro _ ⟨x, -, rfl⟩
      exact x.2
    · exact Subgroup.isPerfect_iff.mpr (by rw [← Subgroup.map_commutator, hDlperf])
    · rw [hsub]
      exact hDlJ
    · rw [hsub, hDlK, Subgroup.subgroupOf_map_subtype]
      exact (inf_of_le_left hKN').symm
    · intro h hh
      exact mem_normalizer_map_br H.subtype (hDln h hh)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
