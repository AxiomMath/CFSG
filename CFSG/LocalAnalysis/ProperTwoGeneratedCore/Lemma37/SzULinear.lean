module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzUSetting
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzUModels
public import CFSG.StronglyEmbedded.MatrixGroups.PSU3Model
public import Certificates.Certificate43
public import Certificates.Certificate113
public import CFSG.Assembly.OrderReductions.CharacterInflation
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartOne
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerBenderComponent
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseTwo
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseTwoComponent
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.Statement
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineCanonicalRank
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionInvolutionCountAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.Statement
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.StrongEmbeddingRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.StronglyEmbedded
public import CFSG.Walter.J1

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.BenderSuzuki
open CFSG.BenderSuzuki.MatrixGroups

theorem exists_pow_eq_one_of_mem_escapingSylowImage {G : Type} [Group G] {S : Sylow 2 G} {z : G}
    {w : EscapingQuotient z} (hw : w ∈ escapingSylowImage S z) : ∃ a : ℕ, w ^ 2 ^ a = 1 := by
  have hP : IsPGroup 2 (escapingSylowImage S z) :=
    (S.isPGroup'.comap_subtype (K := Subgroup.centralizer ({z} : Set G))).map _
  obtain ⟨a, ha⟩ := hP ⟨w, hw⟩
  exact ⟨a, by simpa using congrArg Subtype.val ha⟩

section CaseI

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  (hset : CoreSetting G S H) (hz : IsCentralInvolution (S : Subgroup G) z)
  (hesc : ¬ Subgroup.centralizer ({z} : Set G) ≤ H) {J : Subgroup (EscapingQuotient z)}
  (hJ : CFSG.IsComponent J) (hzJ : escapingBar z ∉ J)
include hset hz hesc hJ hzJ

theorem caseI_not_suzuki
    {m : ℕ} (hm : 1 ≤ m) (e : J ≃* SuzukiMatrixGroup m) : False := by
  have hq := escapingQuotientData hset (hset.sylow_le hz.1) hz.2.1 hesc
  have := hq.component_normal hJ hzJ
  have hS : escapingSylowImage S z ≤ J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z)) := by
    intro w hw
    obtain ⟨a, ha⟩ := exists_pow_eq_one_of_mem_escapingSylowImage hw
    exact mem_sup_centralizer_of_odd_outer (odd_card_outer_of_mulEquiv_suzukiMatrixGroup hm e) ha
  exact false_of_sylow_le_component_sup_centralizer hset hz hesc hJ hzJ hS
    (Nat.even_pow.mpr ⟨even_two, by omega⟩) (by positivity)
    (fun R => (benderRootData_of_mulEquiv_suzukiMatrixGroup m (by omega) e R).1)
    (Or.inr fun R => (benderRootData_of_mulEquiv_suzukiMatrixGroup m (by omega) e R).2)

theorem caseI_not_unitary_of_le {E : Type} [Field E] [Finite E] (U : HermitianForm 3 E)
    {f : ℕ} (hf : 2 ≤ f) (hU : U.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hEcard : Nat.card E = (2 ^ f) ^ 2) (hfixed : Nat.card {x : E // U.conj x = x} = 2 ^ f)
    (e : J ≃* ProjectiveSpecialUnitaryMatrixGroup U)
    (hS : escapingSylowImage S z ≤ J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z))) :
    False := by
  have := Fintype.ofFinite E
  have : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    rw [← Nat.card_eq_fintype_card, hEcard, ← pow_mul])
  have hq0 : 0 < 2 ^ f := by positivity
  refine false_of_sylow_le_component_sup_centralizer hset hz hesc hJ hzJ hS
    (Nat.even_pow.mpr ⟨even_two, by omega⟩) (by positivity)
    (fun R => benderRootData_of_mulEquiv_projectiveSpecialUnitary U hf hEcard hfixed hU e R)
    (Or.inl fun h => ?_)
  have h1 : 2 ^ f * (2 ^ f + 1) = 2 ^ f * 1 := by rw [mul_one, h]
  have h2 := Nat.eq_of_mul_eq_mul_left hq0 h1
  omega

end CaseI

theorem caseILinear
    (h78 : CaseIUnitaryOuterExcluded) : CaseILinear := by
  intro G _ _ S H z hset hz hesc J hJ hzJ
  have hq := escapingQuotientData hset (hset.sylow_le hz.1) hz.2.1 hesc
  rcases hq.component_isSimpleBenderGroup hJ hzJ with ⟨⟨n, hn, ⟨e⟩⟩⟩ | ⟨⟨m, hm, ⟨e⟩⟩⟩ |
      ⟨⟨f, hf, E, hEfield, hEfinite, U, hU, hEcard, hfixed, ⟨e⟩⟩⟩
  · exact ⟨n, hn, ⟨e⟩⟩
  · exact (caseI_not_suzuki hset hz hesc hJ hzJ hm e).elim
  · let : Field E := hEfield
    let : Finite E := hEfinite
    by_cases hS : escapingSylowImage S z ≤ J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z))
    · exact (caseI_not_unitary_of_le hset hz hesc hJ hzJ U hf hU hEcard hfixed e hS).elim
    · obtain ⟨u⟩ := projectiveSpecialUnitary_equiv_PSU3Model U f hf hU hEcard hfixed
      exact (h78 G S H z hset hz hesc J hJ hzJ ⟨f, ⟨e.trans u⟩⟩ hS).elim

end CFSG.ProperTwoGeneratedCore.Lemma37
