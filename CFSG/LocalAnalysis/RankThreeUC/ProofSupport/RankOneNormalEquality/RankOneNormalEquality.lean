module

public import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon
public import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ResidualConjugateClosure.ResidualConjugateClosure
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.OrderThreeFusionInRankOne.OrderThreeFusionInRankOne
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.Basic
import Mathlib.Tactic.NormNum
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.RankOneNormalEquality

open CFSG.LocalAnalysis.RankThreeUC

theorem normal_eq_of_card_eq {G : Type} [Group G] [Finite G] {K A B : Subgroup G}
    (hAK : A ≤ K) (hBK : B ≤ K) [(A.subgroupOf K).Normal] [(B.subgroupOf K).Normal]
    (hr : CFSG.Open.pRank 3 K ≤ 1) (hA : SourceSetting.oPrimeResidual 3 A = A)
    (hB : SourceSetting.oPrimeResidual 3 B = B) (hcard : Nat.card A = Nat.card B) : A = B := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcyc : ∀ Q : Sylow 3 K, IsCyclic ↥(Q : Subgroup K) := by
    intro Q
    have h1 : CFSG.pRank 3 K ≤ 1 := by
      rw [(CFSG.SectionRank.pRank_eq_open_pRank_top 3 K).trans
        (CFSG.SectionRank.pRank_eq_pRank_top_subgroup K).symm]; exact hr
    exact CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.isCyclic_sylow_of_pRank_le_one (by norm_num) (by norm_num) h1 Q
  have hkey : ∀ (N : Subgroup G) (hNK : N ≤ K) [(N.subgroupOf K).Normal] (Q : Sylow 3 K),
      Nat.card ↥((N.subgroupOf K).subgroupOf (Q : Subgroup K)) =
        3 ^ Nat.factorization (Nat.card N) 3 := by
    intro N hNK _ Q
    set Ak : Subgroup K := N.subgroupOf K with hAkdef
    let S := CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal Q Ak
    have hS : (S : Subgroup ↥Ak) = (Q : Subgroup K).subgroupOf Ak :=
      CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal_coe Q Ak
    have h1 : Nat.card ↥(Ak.subgroupOf (Q : Subgroup K)) =
        Nat.card ↥((Q : Subgroup K).subgroupOf Ak) := by
      have e1 : Nat.card ↥((Q : Subgroup K).subgroupOf Ak) =
          Nat.card ↥(((Q : Subgroup K).subgroupOf Ak).map Ak.subtype) :=
        (Subgroup.card_map_of_injective Ak.subtype_injective).symm
      have e2 : Nat.card ↥(Ak.subgroupOf (Q : Subgroup K)) =
          Nat.card ↥((Ak.subgroupOf (Q : Subgroup K)).map (Q : Subgroup K).subtype) :=
        (Subgroup.card_map_of_injective (Q : Subgroup K).subtype_injective).symm
      rw [e1, e2, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_comm]
    have h2 : Nat.card ↥((Q : Subgroup K).subgroupOf Ak) = 3 ^ Nat.factorization (Nat.card ↥Ak) 3 := by
      rw [← hS]
      exact Sylow.card_eq_multiplicity S
    have h3 : Nat.card ↥Ak = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv
    rw [h1, h2, h3]
  have hsub : ∀ Q : Sylow 3 K, (A.subgroupOf K).subgroupOf (Q : Subgroup K) =
      (B.subgroupOf K).subgroupOf (Q : Subgroup K) := by
    intro Q
    haveI := hcyc Q
    apply (IsCyclic.subgroup_eq_iff_card_eq).2
    rw [hkey A hAK Q, hkey B hBK Q, hcard]
  have hres : ∀ (X Y : Subgroup G), X ≤ K → Y ≤ K →
      (∀ Q : Sylow 3 K, (X.subgroupOf K).subgroupOf (Q : Subgroup K) =
        (Y.subgroupOf K).subgroupOf (Q : Subgroup K)) →
      SourceSetting.oPrimeResidual 3 Y ≤ X := by
    intro X Y hXK hYK h
    unfold SourceSetting.oPrimeResidual
    rw [Subgroup.closure_le]
    rintro b ⟨hbY, k, hk⟩
    have hbK : b ∈ K := hYK hbY
    let b' : K := ⟨b, hbK⟩
    have hp : IsPGroup 3 (Subgroup.zpowers b') := by
      rw [IsPGroup.iff_card, Nat.card_zpowers]
      refine ⟨k, ?_⟩
      rw [← hk, ← Subgroup.orderOf_coe b']
    obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
    have hb'Q : b' ∈ (Q : Subgroup K) := hQ (Subgroup.mem_zpowers b')
    let qb : (Q : Subgroup K) := ⟨b', hb'Q⟩
    have hmemY : qb ∈ (Y.subgroupOf K).subgroupOf (Q : Subgroup K) := by
      simp only [Subgroup.mem_subgroupOf]
      exact hbY
    rw [← h Q] at hmemY
    simpa [Subgroup.mem_subgroupOf, qb, b'] using hmemY
  have h1 : B ≤ A := by
    have h := hres A B hAK hBK (fun Q => hsub Q)
    rwa [hB] at h
  have h2 : A ≤ B := by
    have h := hres B A hBK hAK (fun Q => (hsub Q).symm)
    rwa [hA] at h
  exact le_antisymm h2 h1

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.RankOneNormalEquality
