module

public import CFSG.CGT.PushingUpLit.SolKNA.Reduce
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XMain
import CFSG.CGT.PushingUp.TwoLocals
import CFSG.LieType.BorelTits.Suzuki
import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
import CFSG.LocalAnalysis.ComponentClassification.Asc76L28
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Sylow
import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.CGT.PushingUpLit.SolK.Inputs
public import CFSG.CGT.PushingUpLit.Statements
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Goldschmidt.StatementsH
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.AS76bHypII
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XTheorem4
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Containment
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveOrbit
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFixedFactorSylowReduction
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian_models
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.S10.Defs
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2S0LeQuotientTorus
public import CFSG.Walter.J1Recog
public import CFSG.Walter.Ree.Thompson2.BaseFin
public import CFSG.Walter.ReeOrder.WardLocal
public import CFSG.Walter.W67.Section8.Prop83
public import Certificates.Certificate110
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3 (exists_isSylowOf_le)
open CFSG.ComponentClassification.AS76b (oUpperTwoPrime isSylowOf_ne_bot_of_even)
open CFSG.ComponentClassification.Asc76 (IsSzOrU3 SylowNormalizes)
open CFSG.ABGLocalTools (IsSylowOf exists_isSylowOf isSylowOf_iff)
open CFSG.Assembly (pCoreOf)
open CFSG.CGT.PushingUpLit.SolKAb (MTOutcome STSetting sylowImg IsCommSubgroup isPGroup_sylowImg)
open CFSG.Open (standardComponentOddCore)
open CFSG.Assembly.LowTwoRank

section Basic

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

theorem standardComponentOddCore_eq_bot (S : STSetting G K) : standardComponentOddCore G = ⊥ := by
  have := S.simple
  refine le_bot_iff.mp (sSup_le fun N hN => ?_)
  obtain ⟨hNn, hNodd⟩ := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h.le
  · exfalso
    have hG : Odd (Nat.card G) := by
      rw [h, Subgroup.card_top] at hNodd
      exact hNodd
    exact (Nat.not_even_iff_odd.mpr (hG.of_dvd_nat (Subgroup.card_subgroup_dvd_card K))) S.tight.1

theorem normalClosure_eq_top (S : STSetting G K) : Subgroup.normalClosure (K : Set G) = ⊤ := by
  have := S.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure (K : Set G)) with h | h
  · exfalso
    have hK : K = ⊥ := le_bot_iff.mp (h ▸ fun x hx => Subgroup.subset_normalClosure hx)
    have := S.tight.1
    rw [hK, Subgroup.card_bot] at this
    exact Nat.not_even_one this
  · exact h

end Basic

section Theorem1


variable {G : Type} [Group G] [Finite G] {K R : Subgroup G}

theorem exists_J_or_szU3 (S : STSetting G K) (hK : oUpperTwoPrime K = K)
    (hR : IsSylowOf 2 R K) (hnc : ¬ IsCommSubgroup R) (hrk : 2 ≤ CFSG.Open.pRank 2 R) :
    IsSzOrU3 G ∨ ∃ (g : G) (T : Subgroup G), g ∉ Subgroup.normalizer (K : Set G) ∧
      IsSylowOf 2 T (rightConjugate K g ⊓ Subgroup.normalizer (K : Set G)) ∧ T ≠ ⊥ ∧
      Nat.card T < Nat.card R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := S.simple
  by_cases hSz : IsSzOrU3 G
  · exact Or.inl hSz
  refine Or.inr ?_
  by_contra hcon
  have hcon' : ∀ (g : G) (T : Subgroup G), g ∉ Subgroup.normalizer (K : Set G) →
      IsSylowOf 2 T (rightConjugate K g ⊓ Subgroup.normalizer (K : Set G)) → T ≠ ⊥ →
      Nat.card R ≤ Nat.card T := fun g T hg hT hT1 =>
    not_lt.mp fun hlt => hcon ⟨g, T, hg, hT, hT1, hlt⟩
  have hstar : ∀ g : G,
      Even (Nat.card ↥(rightConjugate K g ⊓ Subgroup.normalizer (K : Set G))) →
      SylowNormalizes (rightConjugate K g) K := by
    intro g heven
    by_cases hg : g ∈ Subgroup.normalizer (K : Set G)
    · refine ⟨R, ?_, hR.le.trans Subgroup.le_normalizer⟩
      rw [(rightConjugate_eq_self_iff K g).mpr hg]
      exact hR
    · obtain ⟨T, hT⟩ := exists_isSylowOf 2
        (rightConjugate K g ⊓ Subgroup.normalizer (K : Set G))
      have hT1 : T ≠ ⊥ := isSylowOf_ne_bot_of_even hT heven
      have hRT := hcon' g T hg hT hT1
      obtain ⟨S', hS', hTS'⟩ := exists_isSylowOf_le hT.isPGroup (hT.le.trans inf_le_left)
      have hSR : Nat.card S' = Nat.card R := by
        rw [hS'.card_eq, hR.card_eq, rightConjugate_card]
      have hTS'eq : T = S' := Subgroup.eq_of_le_of_card_ge hTS' (hSR ▸ hRT)
      refine ⟨T, ?_, hT.le.trans inf_le_right⟩
      rw [hTS'eq]
      exact hS'
  have h1 := CFSG.ComponentClassification.Asc76X.asc76Theorem1_of_lemma28
    CFSG.ComponentClassification.Asc76.asc76Lemma28 G K S.tight (normalClosure_eq_top S) hK
    (standardComponentOddCore_eq_bot S) hstar R hR (by omega)
  rcases h1 with hKtop | hel | ⟨hSz', -⟩
  · refine CFSG.CGT.PushingUp.ne_top_of_isPLocal S.nonab S.max.1 ?_
    rw [hKtop]
    exact Subgroup.normalizer_eq_top_iff.mpr inferInstance
  · exact hnc fun a ha b hb => congrArg Subtype.val (hel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  · exact hSz hSz'

end Theorem1

section Outcome

variable {G : Type} [Group G]

theorem stated_of_isSzOrU3 (h : IsSzOrU3 G) :
    (∃ s : ℕ, Odd s ∧ 3 ≤ s ∧ CFSG.Blueprint.LieModel G .twistedB2 0 2 s) ∨
      (∃ s : ℕ, 2 ≤ s ∧ StatedClassicalModel G .PSU 3 2 s) := by
  rcases h with ⟨a, ha, he⟩ | ⟨f, hf, he⟩
  · left
    obtain ⟨a', ha', K', _, _, hcard, ⟨e'⟩⟩ :=
      CFSG.ShultStronglyClosedTI.explicitSuzukiModel_iff.mpr ⟨a, ha, he⟩
    refine ⟨2 * a' + 1, ⟨a', rfl⟩, by omega, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, a', ha', K',
      inferInstance, inferInstance, rfl, hcard, ⟨e'.trans (MulEquiv.subgroupCongr
        (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a' K').symm)⟩⟩))⟩
  · right
    obtain ⟨f', hf', K', _, _, hcard, ⟨e'⟩⟩ :=
      CFSG.ShultStronglyClosedTI.explicitUnitaryModel_iff.mpr ⟨f, hf, he⟩
    refine ⟨f', hf', ⟨Nat.prime_two, by omega, le_rfl, fun hne => ?_⟩, K', inferInstance,
      inferInstance, by rw [hcard, ← pow_mul, mul_comm], ⟨e'⟩⟩
    have h2 : 2 ^ 2 ≤ 2 ^ f' := Nat.pow_le_pow_right (by norm_num) hf'
    have h3 : 2 ^ f' = 2 := (Prod.mk.inj hne).2
    omega

end Outcome

section SzU3Outcome

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

open CFSG.LieType.BorelTits in
theorem sylowImg_eq_pCoreOf_of_isSzOrU3 (S : STSetting G K)
    (hSz : IsSzOrU3 G) (R : Sylow 2 K) : sylowImg R = pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmax := S.max
  obtain ⟨P₀, hP₀, hP₀2, hMP₀⟩ := hmax.1
  have hKM : K ≤ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer
  generalize hM : Subgroup.normalizer (K : Set G) = M at hmax hMP₀ hKM
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := le_of_eq hM.symm
  have hP₀Q : P₀ ≤ pCoreOf 2 M := by
    rw [hMP₀]
    exact le_pCoreOf_normalizer 2 P₀ hP₀2
  have hQne : pCoreOf 2 M ≠ ⊥ := fun h => hP₀ (le_bot_iff.mp (h ▸ hP₀Q))
  have hQ2 : IsPGroup 2 (pCoreOf 2 M) := pCoreOf_isPGroup 2 M
  have hMQ : Subgroup.normalizer (pCoreOf 2 M : Set G) = M := by
    by_contra hne
    exact hmax.2 _ (lt_of_le_of_ne (le_normalizer_pCoreOf 2 M) (Ne.symm hne))
      ⟨pCoreOf 2 M, hQne, hQ2, rfl⟩
  obtain ⟨P, hQP⟩ := hQ2.exists_le_sylow
  have hPne : (P : Subgroup G) ≠ ⊥ := fun h => hQne (le_bot_iff.mp (h ▸ hQP))
  have hNP : M ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) := by
    intro g hg
    rw [← hMQ] at hg
    refine Sylow.smul_eq_iff_mem_normalizer.mp ?_
    by_contra hne
    have hTI := CFSG.ComponentClassification.Asc76X.benderFacts.sylow_inf G hSz P (g • P)
      (Ne.symm hne)
    refine hQne (le_bot_iff.mp (hTI ▸ le_inf hQP ?_))
    intro x hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have h1 : g⁻¹ * x * g ∈ pCoreOf 2 M := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp hx
      simpa [mul_assoc] using this
    simpa [MulAut.smul_def, mul_assoc] using hQP h1
  have hPM : M = Subgroup.normalizer ((P : Subgroup G) : Set G) := by
    by_contra hne
    exact hmax.2 _ (lt_of_le_of_ne hNP hne) ⟨P, hPne, P.isPGroup', rfl⟩
  have hPleM : (P : Subgroup G) ≤ M := hPM ▸ Subgroup.le_normalizer
  have hPsyl : IsSylowOf 2 (P : Subgroup G) M :=
    isSylowOf_iff.mpr ⟨hPleM, P.isPGroup', fun h => P.not_dvd_index
      (h.trans (Subgroup.relIndex_dvd_index_of_le hPleM))⟩
  have hPK : IsSylowOf 2 ((P : Subgroup G) ⊓ K) K :=
    hPsyl.inf_of_le_normalizer hKM hMK
  have hPKO : (P : Subgroup G) ⊓ K ≤ pCoreOf 2 K := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ (P.isPGroup'.to_inf_left)
    intro k hk
    exact CFSG.RankThree.GF2n.mem_normalizer_inf (hPM ▸ hKM hk) (Subgroup.le_normalizer hk)
  have hOR : pCoreOf 2 K ≤ sylowImg R := by
    have hnorm : (CFSG.Open.pCore 2 K).Normal := CFSG.LieType.BorelTits.pCore_normal 2
    have hle : CFSG.Open.pCore 2 K ≤ (R : Subgroup K) :=
      (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := K)).le_sylow_of_normal R
    exact Subgroup.map_mono hle
  have hRsyl : IsSylowOf 2 (sylowImg R) K := ⟨R, rfl⟩
  have hcard : Nat.card (sylowImg R) ≤ Nat.card (pCoreOf 2 K) := by
    rw [hRsyl.card_eq, ← hPK.card_eq]
    exact Subgroup.card_le_of_le hPKO
  exact (Subgroup.eq_of_le_of_card_ge hOR hcard).symm

theorem szU3_outcome (S : STSetting G K) (hSz : IsSzOrU3 G)
    (R : Sylow 2 K) : Outcome6 G K (sylowImg R) :=
  ⟨sylowImg_eq_pCoreOf_of_isSzOrU3 S hSz R, stated_of_isSzOrU3 hSz⟩

theorem szU3_mtOutcome (S : STSetting G K) (hSz : IsSzOrU3 G)
    (R : Sylow 2 K) : MTOutcome G K R :=
  mtOutcome_of_outcome56 R (Or.inr (szU3_outcome S hSz R))

end SzU3Outcome

end CFSG.CGT.PushingUpLit.SolKNA
