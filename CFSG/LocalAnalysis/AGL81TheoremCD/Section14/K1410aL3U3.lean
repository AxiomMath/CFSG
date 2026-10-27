module

public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
import CFSG.GroupTheory.ExtraspecialThreeFive
import CFSG.RankThree.PartTwo.Sec4.E27.L3FLinear
import CFSG.RankThree.PartTwo.Sec4.E27.L3FUnitaryCount
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneFourteenTen
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LieType.SeitzGeneration.Hyper
import CFSG.LieType.SeitzGeneration.HyperBridge
import CFSG.LieType.SeitzGeneration.HyperOuterFieldAut
import CFSG.LieType.SeitzGeneration.Inner
import CFSG.LieType.SeitzGeneration.OuterModel
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenAssembly
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3FourGenData
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
import CFSG.LocalAnalysis.RankThreeTheoremC.D1Frontier3
import CFSG.Quasithin.Background.A3Structure36BPrime
import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
import CFSG.RankThree.PartOne.CTP.SeitzFineU5
import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
import CFSG.RankThree.PartOne.KF.SU5Model
import CFSG.RankThree.PartOne.N143.LowTwoRankSplit
import CFSG.RankThree.PartOne.N143.SectionCenter
import CFSG.RankThree.PartOne.N143.SectionRankBound
import CFSG.RankThree.PartOne.N143.SectionRankProof
import CFSG.RankThree.PartOne.N143.SectionRankSplit
import CFSG.RankThree.PartOne.N143.SectionReduce
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartTwo.Sec14.Item148Steps
import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofFaithNF
import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoL8
import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoU10
import CFSG.RankThree.PartTwo.Sec19.Step1914Split
import CFSG.RankThree.PartTwo.Sec19.Step199Proof
import CFSG.RankThree.PartTwo.Sec21.Item229Diagram
import CFSG.RankThree.PartTwo.Sec21.Membership
import CFSG.RankThree.PartTwo.Sec21.SylowThree
import CFSG.RankThree.PartTwo.Sec4.Census.Open43
import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.Sporadic.Schreier.TitsOther
import Certificates.Certificate10019
import Certificates.Certificate10019Base
import Certificates.Certificate2202

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartTwo.KFacts Matrix
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4.E27

private theorem isThreeOnePlusFour_map_congr {X Y : Type} [Group X] [Group Y]
    (e : X ≃* Y) {T : Subgroup (MulAut X)}
    (hT : S15.IsThreeOnePlusFour ↥T) :
    S15.IsThreeOnePlusFour ↥(T.map (MulAut.congr e).toMonoidHom) :=
  isThreeOnePlusFour_of_mulEquiv
    (Subgroup.equivMapOfInjective T (MulAut.congr e).toMonoidHom
      (MulAut.congr e).injective) hT

theorem card_le_three_mul_card_inf_linear_of_pow_three {F : Type} [Field F] [Finite F]
    {T : Subgroup (MulAut (projectiveSL 3 F))} (hT : ∀ t ∈ T, t ^ 3 = 1) :
    Nat.card T ≤ 3 * Nat.card (T ⊓ linearAutGroup 3 F : Subgroup _) := by
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨p, -, f, hp, hK⟩ := FiniteField.card' F
  haveI : IsCyclic (F ≃+* F) :=
    (card_ringAut_and_isCyclic hp F (by rw [Nat.card_eq_fintype_card, hK])).2
  have hcyc : IsCyclic (fieldAut 3 F).range :=
    isCyclic_of_surjective (fieldAut 3 F).rangeRestrict (fieldAut 3 F).rangeRestrict_surjective
  have hCN : (fieldAut 3 F).range ≤
      Subgroup.normalizer
        ((linearAutGroup 3 F : Subgroup _) : Set (MulAut (projectiveSL 3 F))) := by
    have key : ∀ σ : F ≃+* F, ∀ x ∈ linearAutGroup 3 F,
        fieldAut 3 F σ * x * (fieldAut 3 F σ)⁻¹ ∈ linearAutGroup 3 F := by
      intro σ x hx
      rw [Sec4.linearAutGroup_three_eq_range] at hx ⊢
      obtain ⟨A, rfl⟩ := hx
      refine ⟨Matrix.GeneralLinearGroup.map (σ : F →+* F) A, ?_⟩
      rw [fieldAut_mul_conjAut, mul_inv_cancel_right]
    rintro _ ⟨σ, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key σ x, fun hx => ?_⟩
    have h := key σ⁻¹ (fieldAut 3 F σ * x * (fieldAut 3 F σ)⁻¹) hx
    rw [map_inv] at h
    have e : (fieldAut 3 F σ)⁻¹ * (fieldAut 3 F σ * x * (fieldAut 3 F σ)⁻¹) *
        ((fieldAut 3 F σ)⁻¹)⁻¹ = x := by group
    rw [e] at h
    exact h
  have hBNC : ∀ b ∈ T, ∃ n ∈ linearAutGroup 3 F, ∃ c ∈ (fieldAut 3 F).range, b = n * c := by
    intro b hb
    by_cases hbN : b ∈ linearAutGroup 3 F
    · exact ⟨b, hbN, 1, one_mem _, (mul_one b).symm⟩
    · obtain ⟨σ, -, H, hH⟩ :=
        KFacts.linear_order_three_field_descent (by norm_num) b (hT b hb) hbN
      refine ⟨conjAut 3 F H * conjAut 3 F (Matrix.GeneralLinearGroup.map (σ : F →+* F) H⁻¹),
        ?_, fieldAut 3 F σ, ⟨σ, rfl⟩, ?_⟩
      · rw [Sec4.linearAutGroup_three_eq_range]
        exact ⟨_, map_mul _ _ _⟩
      · rw [hH, ← map_inv, mul_assoc, fieldAut_mul_conjAut, ← mul_assoc]
  exact CFSG.GroupTheory.ExtraspecialThreeFive.card_le_three_mul_card_inf_of_pow_three
    hT hcyc hCN hBNC

theorem card_le_three_mul_card_inf_psu_of_pow_three {p f : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData p f K} (hq : 2 < p ^ f)
    {T : Subgroup (MulAut (unitaryPSU h 3))} (hT : ∀ t ∈ T, t ^ 3 = 1) :
    Nat.card T ≤
      3 * Nat.card (T ⊓ (CFSG.RankThree.PartTwo.KFacts.psuConj h).range : Subgroup _) := by
  haveI : Finite K := h.finite
  haveI : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic h.prime K h.card).2
  set N := (psuConj h).range with hNdef
  set C := (psuField h).range with hCdef
  have hcyc : IsCyclic C :=
    isCyclic_of_surjective (psuField h).rangeRestrict (psuField h).rangeRestrict_surjective
  have hCN : C ≤ Subgroup.normalizer (N : Set (MulAut (unitaryPSU h 3))) := by
    rintro _ ⟨σ, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact SetLike.mem_coe.mpr (Sec19.seitzU1_psuField_conj_mem σ (SetLike.mem_coe.mp hx))
    · intro hx
      have h2 := Sec19.seitzU1_psuField_conj_mem σ⁻¹ (SetLike.mem_coe.mp hx)
      rw [map_inv] at h2
      have e : (psuField h σ)⁻¹ * (psuField h σ * x * (psuField h σ)⁻¹) *
          ((psuField h σ)⁻¹)⁻¹ = x := by group
      rw [e] at h2
      exact SetLike.mem_coe.mpr h2
  have hBNC : ∀ b ∈ T, ∃ n ∈ N, ∃ c ∈ C, b = n * c := by
    intro b _
    obtain ⟨A, σ, hAσ⟩ := exists_psuConj_mul_psuField hq b
    exact ⟨psuConj h A, ⟨A, rfl⟩, psuField h σ, ⟨σ, rfl⟩, hAσ⟩
  exact CFSG.GroupTheory.ExtraspecialThreeFive.card_le_three_mul_card_inf_of_pow_three
    hT hcyc hCN hBNC

theorem false_of_threeOnePlusFour_projectiveSL_three {F : Type} [Field F] [Finite F]
    (h3 : (3 : F) ≠ 0) {T : Subgroup (MulAut (projectiveSL 3 F))}
    (hT : S15.IsThreeOnePlusFour ↥T) : False := by
  obtain ⟨hcard, hexp, hZ, hcomm⟩ := hT
  have hpow : ∀ t ∈ T, t ^ 3 = 1 := fun t ht => by simpa using hexp ⟨t, ht⟩
  have hcount := card_le_three_mul_card_inf_linear_of_pow_three (F := F) hpow
  obtain ⟨E, hE, hEea, hEcard⟩ :=
    CFSG.GroupTheory.ExtraspecialThreeFive.exists_elemAbelian_27_le_inf (R := T)
      (N := linearAutGroup 3 F) hcard hexp hZ hcomm hcount
  exact not_le_linearAutGroup_of_card h3 hEea (by rw [hEcard]; norm_num)
    (hE.trans inf_le_right)

theorem false_of_threeOnePlusFour_psu_three {p f : ℕ} {K : Type} [Field K] [Finite K]
    {h : UnitaryFieldData p f K} (h3 : (3 : K) ≠ 0) (hq : 2 < p ^ f)
    {T : Subgroup (MulAut (unitaryPSU h 3))} (hT : S15.IsThreeOnePlusFour ↥T) : False := by
  obtain ⟨hcard, hexp, hZ, hcomm⟩ := hT
  have hpow : ∀ t ∈ T, t ^ 3 = 1 := fun t ht => by simpa using hexp ⟨t, ht⟩
  have hcount := card_le_three_mul_card_inf_psu_of_pow_three (h := h) hq hpow
  obtain ⟨E, hE, hEea, hEcard⟩ :=
    CFSG.GroupTheory.ExtraspecialThreeFive.exists_elemAbelian_27_le_inf (R := T)
      (N := (psuConj h).range) hcard hexp hZ hcomm hcount
  exact not_le_psuConj_range_of_card h3 hEea (by rw [hEcard]; norm_num)
    (hE.trans inf_le_right)

theorem false_of_statedClassicalModel_psl_three {Y : Type} [Group Y] {f : ℕ}
    (hm : CFSG.Open.StatedClassicalModel Y .PSL 3 2 f) {T : Subgroup (MulAut Y)}
    (hT : S15.IsThreeOnePlusFour ↥T) : False := by
  obtain ⟨-, K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := hm
  letI := hKfield
  haveI := hKfin
  let e' : Y ≃* projectiveSL 3 K :=
    (e.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)
  have h3 : (3 : K) ≠ 0 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fintype K := Fintype.ofFinite K
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by
      rw [← Nat.card_eq_fintype_card, hKcard])
    intro h
    have hdvd : 2 ∣ 3 := (CharP.cast_eq_zero_iff K 2 3).mp h
    norm_num at hdvd
  exact false_of_threeOnePlusFour_projectiveSL_three h3 (isThreeOnePlusFour_map_congr e' hT)

theorem false_of_statedClassicalModel_psu_three {Y : Type} [Group Y] {f : ℕ}
    (hm : CFSG.Open.StatedClassicalModel Y .PSU 3 2 f) {T : Subgroup (MulAut Y)}
    (hT : S15.IsThreeOnePlusFour ↥T) : False := by
  obtain ⟨hadm, K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := hm
  letI := hKfield
  haveI := hKfin
  obtain ⟨-, hf1, -, hne⟩ := hadm
  have hf_ne_one : f ≠ 1 := by
    rintro rfl
    exact hne (by norm_num)
  have hf2 : 2 ≤ f := by
    have h1 : 1 < f := lt_of_le_of_ne hf1 (Ne.symm hf_ne_one)
    omega
  have hq : 2 < 2 ^ f := by
    have h : 2 ^ 1 < 2 ^ f := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega)
    simpa using h
  have hU : UnitaryFieldData 2 f K :=
    ⟨Nat.prime_two, hf1, by rw [hKcard, ← pow_mul, mul_comm]⟩
  have h3 : (3 : K) ≠ 0 := by
    haveI : CharP K 2 := hU.charP
    intro h
    have hdvd : 2 ∣ 3 := (CharP.cast_eq_zero_iff K 2 3).mp h
    norm_num at hdvd
  let e' : Y ≃* unitaryPSU hU 3 :=
    e.trans (unitaryPSUEquiv hU (n := 3) (by norm_num)).symm
  exact false_of_threeOnePlusFour_psu_three h3 hq (isThreeOnePlusFour_map_congr e' hT)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
