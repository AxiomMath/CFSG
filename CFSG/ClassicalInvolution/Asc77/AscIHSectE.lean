module

public import CFSG.ClassicalInvolution.Asc77.AscIHSectD
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofPSL
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofPSp
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofPSU
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthBridge
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleClique
public import CFSG.ClassicalInvolution.RouteD.TypeCRecognition
public import CFSG.ClassicalInvolution.RouteD.TypeULocal
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.Asc77.AscE184SecC
public import CFSG.ClassicalInvolution.Asc77.AscIHSectC
public import CFSG.ClassicalInvolution.Asc77.AscSixZW
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.TwinLookup
public import CFSG.ClassicalInvolution.Asc77.WP2Thm7c
public import CFSG.ClassicalInvolution.Asc77.WP2Thompson
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsH
public import CFSG.Goldschmidt.StatementsX
public import CFSG.LocalAnalysis.ComponentClassification.QuasisimpleNormalizerCommutator
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

theorem noThree_psl4 (hp2 : p ≠ 2) {e : ℕ} {A B S : Subgroup (modelUniv .PSL 4 p e Fact.out).K}
    (hA : A ∈ ModelFund p .PSL 4 e) (hB : B ∈ ModelFund p .PSL 4 e)
    (hS : S ∈ ModelFund p .PSL 4 e) (hAB : A ≠ B) (hAS : A ≠ S) (hBS : B ≠ S)
    (cAB : Commutes A B) (cAS : Commutes A S) (cBS : Commutes B S) : False := by
  have h := fundamentalSubgroups_psl_eq (p := p) (f := e) (m := 3) (by norm_num)
  have hA' : A ∈ Models.longRootSet (K := GaloisField p e) (by omega : 2 ≤ 3 + 1) := by
    rw [← h]; exact hA
  have hB' : B ∈ Models.longRootSet (K := GaloisField p e) (by omega : 2 ≤ 3 + 1) := by
    rw [← h]; exact hB
  have hS' : S ∈ Models.longRootSet (K := GaloisField p e) (by omega : 2 ≤ 3 + 1) := by
    rw [← h]; exact hS
  obtain ⟨i₀, h₀⟩ := hA'
  obtain ⟨i₁, h₁⟩ := hB'
  obtain ⟨i₂, h₂⟩ := hS'
  exact false_of_commutes_three_four (ModelFacts.two_ne_zero_galoisField e hp2) h₀ h₁ h₂ hAB hAS
    hBS cAB cAS cBS

theorem noThree_psp2 (hp2 : p ≠ 2) {e : ℕ} (hadm : StatedLieAdmissible .PSp 2 p e)
    {A B S : Subgroup (modelUniv .PSp 2 p e Fact.out).K} (hA : A ∈ ModelFund p .PSp 2 e)
    (hB : B ∈ ModelFund p .PSp 2 e) (hS : S ∈ ModelFund p .PSp 2 e) (hAB : A ≠ B) (hAS : A ≠ S)
    (hBS : B ≠ S) (cAB : Commutes A B) (cAS : Commutes A S) (cBS : Commutes B S) : False := by
  have h := fundamentalSubgroups_psp_eq (p := p) (f := e) hadm
  have hA' : A ∈ planeGroupSet (GaloisField p e) 2 := by rw [← h]; exact hA
  have hB' : B ∈ planeGroupSet (GaloisField p e) 2 := by rw [← h]; exact hB
  have hS' : S ∈ planeGroupSet (GaloisField p e) 2 := by rw [← h]; exact hS
  have h2 := ModelFacts.two_ne_zero_galoisField e hp2
  obtain ⟨P₀, hP₀, rfl⟩ := hA'
  obtain ⟨P₁, hP₁, rfl⟩ := hB'
  obtain ⟨P₂, hP₂, rfl⟩ := hS'
  exact false_of_orth_three_two hP₀ hP₁ hP₂
    ((commutes_planeGroup_iff h2 hP₀ hP₁ (fun e => hAB (by rw [e]))).mp cAB)
    ((commutes_planeGroup_iff h2 hP₀ hP₂ (fun e => hAS (by rw [e]))).mp cAS)
    ((commutes_planeGroup_iff h2 hP₁ hP₂ (fun e => hBS (by rw [e]))).mp cBS)

theorem noThree_psu4 (hp2 : p ≠ 2) {e : ℕ} (hadm : StatedLieAdmissible .PSU 4 p e)
    {A B S : Subgroup (modelUniv .PSU 4 p e Fact.out).K} (hA : A ∈ ModelFund p .PSU 4 e)
    (hB : B ∈ ModelFund p .PSU 4 e) (hS : S ∈ ModelFund p .PSU 4 e) (hAB : A ≠ B) (hAS : A ≠ S)
    (hBS : B ≠ S) (cAB : Commutes A B) (cAS : Commutes A S) (cBS : Commutes B S) : False := by
  have hf : 1 ≤ e := hadm.2.1
  have hK := CFSG.LieType.Universal.card_galoisField_two_mul p e hf
  obtain ⟨φ, hφ⟩ := psu_model_equiv hp2 hadm
  have hn : 2 ≤ 4 := by norm_num
  have hn3 : 3 ≤ 4 := by norm_num
  obtain ⟨V₀, n₀, d₀, e₀⟩ := (mem_longRootSetU_iff_plane hK hp2 hn).mp ((hφ A).mp hA)
  obtain ⟨V₁, n₁, d₁, e₁⟩ := (mem_longRootSetU_iff_plane hK hp2 hn).mp ((hφ B).mp hB)
  obtain ⟨V₂, n₂, d₂, e₂⟩ := (mem_longRootSetU_iff_plane hK hp2 hn).mp ((hφ S).mp hS)
  have c01 := (commutes_map_equiv φ).mpr cAB
  have c02 := (commutes_map_equiv φ).mpr cAS
  have c12 := (commutes_map_equiv φ).mpr cBS
  rw [e₀, e₁] at c01
  rw [e₀, e₂] at c02
  rw [e₁, e₂] at c12
  have hV01 : V₀ ≠ V₁ := fun h => hAB (Subgroup.map_injective φ.injective (by rw [e₀, e₁, h]))
  have hV02 : V₀ ≠ V₂ := fun h => hAS (Subgroup.map_injective φ.injective (by rw [e₀, e₂, h]))
  have hV12 : V₁ ≠ V₂ := fun h => hBS (Subgroup.map_injective φ.injective (by rw [e₁, e₂, h]))
  exact false_of_orth_three_four n₁ n₂ d₀ d₁ d₂
    ((commutes_planeGroupU_iff hK hp2 hn hn3 n₀ d₀ n₁ d₁ hV01).mp c01)
    ((commutes_planeGroupU_iff hK hp2 hn hn3 n₀ d₀ n₂ d₂ hV02).mp c02)
    ((commutes_planeGroupU_iff hK hp2 hn hn3 n₁ d₁ n₂ d₂ hV12).mp c12)

section Orth

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem false_of_commuting_three_fundSet (hodd : Odd (Nat.card K))
    (hsame : ∀ (R₀ R₁ : Subgroup (V ≃ₗ[K] V)) (i₀ i₁ : V ≃ₗ[K] V), IsFundamental Q R₀ i₀ →
      IsFundamental Q R₁ i₁ → Commutes R₀ R₁ → i₁ = i₀)
    {R₀ R₁ R₂ : Subgroup (V ≃ₗ[K] V)} (h₀ : R₀ ∈ fundSet Q) (h₁ : R₁ ∈ fundSet Q)
    (h₂ : R₂ ∈ fundSet Q) (n01 : R₀ ≠ R₁) (n02 : R₀ ≠ R₂) (n12 : R₁ ≠ R₂)
    (c01 : Commutes R₀ R₁) (c02 : Commutes R₀ R₂) : False := by
  obtain ⟨i₀, h₀⟩ := h₀
  obtain ⟨i₁, h₁⟩ := h₁
  obtain ⟨i₂, h₂⟩ := h₂
  have e1 : i₁ = i₀ := hsame R₀ R₁ i₀ i₁ h₀ h₁ c01
  have e2 : i₂ = i₀ := hsame R₀ R₂ i₀ i₂ h₀ h₂ c02
  subst e1 e2
  exact no_three_same hodd h₀ h₁ h₂ n01 n02 n12

end Orth

section Spin

variable {e : ℕ}

theorem commutator_self_eq' {G : Type} [Group G] {R : Subgroup G} (h : R ≤ ⁅R, R⁆) :
    ⁅R, R⁆ = R :=
  le_antisymm (Subgroup.commutator_le.mpr fun _ ha _ hb =>
    R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)) h

theorem clique_map_of_central {X Y : Type} [Group X] [Group Y] (π : X →* Y)
    (hker : π.ker ≤ Subgroup.center X) {A B S : Subgroup X} (hpA : ⁅A, A⁆ = A)
    (hpB : ⁅B, B⁆ = B) (hpS : ⁅S, S⁆ = S) (hAB : A ≠ B) (hAS : A ≠ S) (hBS : B ≠ S)
    (cAB : Commutes A B) (cAS : Commutes A S) :
    A.map π ≠ B.map π ∧ A.map π ≠ S.map π ∧ B.map π ≠ S.map π ∧
      Commutes (A.map π) (B.map π) ∧ Commutes (A.map π) (S.map π) :=
  ⟨fun h => hAB (ModelFacts.eq_of_map_eq_of_isPerfect π hker hpA hpB h),
    fun h => hAS (ModelFacts.eq_of_map_eq_of_isPerfect π hker hpA hpS h),
    fun h => hBS (ModelFacts.eq_of_map_eq_of_isPerfect π hker hpB hpS h),
    ih8_commutes_map π cAB, ih8_commutes_map π cAS⟩

theorem noThree_odd3 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .POmegaOdd 3 p e)
    {A B S : Subgroup (modelUniv .POmegaOdd 3 p e Fact.out).K} (hA : A ∈ ModelFund p .POmegaOdd 3 e)
    (hB : B ∈ ModelFund p .POmegaOdd 3 e) (hS : S ∈ ModelFund p .POmegaOdd 3 e) (hAB : A ≠ B)
    (hAS : A ≠ S) (hBS : B ≠ S) (cAB : Commutes A B) (cAS : Commutes A S) : False := by
  obtain ⟨hodd, h4⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have hperf : Gaps.FundPerfect .POmegaOdd (modelUniv .POmegaOdd 3 p e Fact.out).D :=
    Gaps.fundPerfect_modelUniv hp2 trivial hadm (by omega)
  have hcorr := fundCorr_odd hp2 hq hadm
  have hpA : ⁅A, A⁆ = A := commutator_self_eq' (hperf A hA)
  have hpB : ⁅B, B⁆ = B := commutator_self_eq' (hperf B hB)
  have hpS : ⁅S, S⁆ = S := commutator_self_eq' (hperf S hS)
  obtain ⟨n01, n02, n12, c01, c02⟩ := clique_map_of_central
    (spinAction (quadOdd 3 (GaloisField p e))) (ker_spinAction_le_center _) hpA hpB hpS hAB hAS hBS
    cAB cAS
  have hdim : Module.finrank (GaloisField p e) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p e) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
  exact false_of_commuting_three_fundSet hodd
    (fun _ _ _ _ h₀ h₁ hc => commuting_same_involution hodd (by omega) h₀ h₁ hc)
    (hcorr.1 A hA) (hcorr.1 B hB) (hcorr.1 S hS) n01 n02 n12 c01 c02

theorem noThree_minus4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .POmegaMinus 4 p e)
    {A B S : Subgroup (modelUniv .POmegaMinus 4 p e Fact.out).K}
    (hA : A ∈ ModelFund p .POmegaMinus 4 e) (hB : B ∈ ModelFund p .POmegaMinus 4 e)
    (hS : S ∈ ModelFund p .POmegaMinus 4 e) (hAB : A ≠ B) (hAS : A ≠ S) (hBS : B ≠ S)
    (cAB : Commutes A B) (cAS : Commutes A S) : False := by
  obtain ⟨hodd, h4⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have hperf : Gaps.FundPerfect .POmegaMinus (modelUniv .POmegaMinus 4 p e Fact.out).D :=
    Gaps.fundPerfect_modelUniv hp2 trivial hadm (by omega)
  have hcorr := fundCorr_minus hp2 hq hadm
  have hpA : ⁅A, A⁆ = A := commutator_self_eq' (hperf A hA)
  have hpB : ⁅B, B⁆ = B := commutator_self_eq' (hperf B hB)
  have hpS : ⁅S, S⁆ = S := commutator_self_eq' (hperf S hS)
  obtain ⟨n01, n02, n12, c01, c02⟩ := clique_map_of_central
    (spinAction (quadMinus 4 (GaloisField p e) (minusCoeffs p e).1 (minusCoeffs p e).2))
    (ker_spinAction_le_center _) hpA hpB hpS hAB hAS hBS cAB cAS
  have hNo : ∀ F₀ F₁ : Models.OrthogonalPairs.Frame
      (quadMinus 4 (GaloisField p e) (minusCoeffs p e).1 (minusCoeffs p e).2),
      F₁.span ≤ F₀.perp → False := fun F₀ F₁ hF =>
    false_of_orth_quadMinus_four (ModelFacts.two_ne_zero_galoisField e hp2) (minusCoeffs_irr p e)
      h4 F₀ F₁ hF
  refine false_of_commuting_three_fundSet hodd (fun R₀ R₁ i₀ i₁ h₀ h₁ hc => ?_)
    (hcorr.1 A hA) (hcorr.1 B hB) (hcorr.1 S hS) n01 n02 n12 c01 c02
  rcases Gaps.orth_or_twin hodd h₀ h₁ hc with horth | heq
  · exfalso
    obtain ⟨F₀, rfl, rfl⟩ := h₀
    obtain ⟨F₁, rfl, rfl⟩ := h₁
    exact hNo F₀ F₁ (span_le_perp_of_negSpace hodd horth)
  · exact heq

end Spin

theorem smallNoThree : SmallNoThree p := by
  intro t k e hadm hp2 hq hsmall A hA B hB S hS hAB hAS hBS cAB cAS cBS
  rcases hsmall with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact noThree_psp2 hp2 hadm hA hB hS hAB hAS hBS cAB cAS cBS
  · exact noThree_psl4 hp2 hA hB hS hAB hAS hBS cAB cAS cBS
  · exact noThree_psu4 hp2 hadm hA hB hS hAB hAS hBS cAB cAS cBS
  · exact noThree_odd3 hp2 hq hadm hA hB hS hAB hAS hBS cAB cAS
  · exact noThree_minus4 hp2 hq hadm hA hB hS hAB hAS hBS cAB cAS

end CFSG.ClassicalInvolution.Asc77
