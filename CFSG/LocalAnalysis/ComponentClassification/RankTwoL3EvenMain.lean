module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3EvenAg
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma34
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIL3
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIYCriterion
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicOddCore
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
public import CFSG.LocalAnalysis.ComponentInitial.KProperSubgroup
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.LieType.Ree.SuzukiOrder
public import Certificates.Certificate43
public import Certificates.Certificate113
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutLinear
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitary
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import Certificates.Certificate1
public import Certificates.Certificate2
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoL3Even

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial LinearFlag
  FieldFourCover CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

theorem three_dvd_card_SL2 {F : Type} [Field F] [Finite F] [CharP F 2] :
    3 ∣ Nat.card (SL2 F) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  let M : SL2 F := ⟨!![0, 1; 1, 1], by
    rw [Matrix.det_fin_two_of, zero_mul, one_mul, zero_sub, CharTwo.neg_eq]⟩
  have hM3 : M ^ 3 = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;>
      simp [M, pow_succ, Matrix.mul_apply, Fin.sum_univ_two, h2]
  have hM1 : M ≠ 1 := by
    intro h
    have h00 := congrArg (fun g : SL2 F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp [M] at h00
  rw [← orderOf_eq_prime hM3 hM1]
  exact orderOf_dvd_natCard M

theorem statedClassicalModel_of_mulEquiv_SL2 {F : Type} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 3 ≤ m) (hF : Nat.card F = 2 ^ m) {Q : Type} [Group Q] (e : Q ≃* SL2 F) :
    Assembly.LowTwoRank.StatedClassicalModel Q .PSL 2 2 m := by
  have h8 : 8 ≤ 2 ^ m := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, F, inferInstance, inferInstance, hF,
    ⟨e.trans ((CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := F)).symm.trans
      (projectiveSpecialLinearGroupEquivStatedProj 2 F))⟩⟩
  · intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega
  · intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega

theorem not_three_dvd_card_of_suzukiModel_three {X : Type}
    [Group X] (h : SuzukiModel X 2 3) : ¬ 3 ∣ Nat.card X := by
  obtain ⟨-, a, -, K, _, _, hn, hK, ⟨e⟩⟩ := h
  obtain rfl : a = 1 := by omega
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order (a := 1) (K := K) hK]
  norm_num

theorem two_le_pRank_centralizer_subgroupOf {G : Type} [Group G] [Finite G] {A W L : Subgroup G}
    (hWA : W ≤ A) (hLA : L ≤ A) (hrank : 2 ≤ Open.pRank 2 (centralizer (A : Set G))) :
    2 ≤ Open.pRank 2 (centralizer ((L.subgroupOf (centralizer (W : Set G)) :
      Subgroup ↥(centralizer (W : Set G))) : Set ↥(centralizer (W : Set G)))) := by
  obtain ⟨U, hUK, hU, hU4⟩ := exists_four_le_of_two_le_pRank hrank
  have hUW : U ≤ centralizer (W : Set G) := hUK.trans (centralizer_le hWA)
  refine CFSG.SectionRank.le_pRank one_lt_two (E := U.subgroupOf (centralizer (W : Set G)))
    ?_ ?_ ?_
  · intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (mem_centralizer_iff.1 (hUK (mem_subgroupOf.1 hx)) y
      (hLA (mem_subgroupOf.1 hy)))
  · refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · have h := congrArg Subtype.val (hU.1.is_comm.comm ⟨a.1.1, a.2⟩ ⟨b.1.1, b.2⟩)
      simpa using h
    · simpa using hU.2 _ hx
  · rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hU4]
    exact Nat.card_congr (subgroupOfEquivOfLe hUW).toEquiv

theorem l3_part_one_of_foundation
    (h3 : AS76b.Section3Config) (h32 : AS76b.Lemma32) (h4 : AS76b.Asc75Theorem4)
    (hB : RankTwoBenderStandard) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHyp G A → ∀ m : ℕ, 3 ≤ m →
      Assembly.LowTwoRank.StatedClassicalModel (rankTwoQuot A) .PSL 3 2 m →
        standardComponentOddCore G = ⊥ → False := by
  intro G _ _ A hH m hm hQ hO
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := id hQ
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have h4K : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : Group.IsPerfect (SL2 K) := isPerfect_SL2 h4K
  have : IsSimpleGroup (SL2 K) := RankTwoHypIIL3.isSimpleGroup_SL2 h4K
  let e : ↥A ⧸ center ↥A ≃* projectiveSL 3 K :=
    e₀.trans ((projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K))
  obtain ⟨ψ, hψ⟩ := exists_isActionHom
    (RankTwoHypIIY.autModel_mulAut (RankTwoHypIIL3.center_projectiveSL_three_eq_bot K))
    hH.standard.1.1 e
  have hA := hH.standard
  have hA31 : AS76b.Hyp31 A := ⟨hA, RankTwoHypIIL3.hypII_L3 hA.1.1 hm hQ, hO,
    lt_of_lt_of_le one_lt_two hH.rank, hH.not_normal⟩
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rw [card_inf_centralizer_eq]
    exact odd_card_center_of_psl3 hA.1.1 hm hQ
  have hKey := odd_card_inf_rightConjugate_centralizer hA hψ hZ (h32 G A hA31) hm hK
  obtain ⟨g, hg, R, T, hR, hT, hTN, hRN, hTR, -, -⟩ := h3 G A hA31
  have htight := AS76b.tightlyEmbedded_centralizer hA
  have hR1 : R ≠ ⊥ := AS76b.isSylowOf_ne_bot_of_even hR htight.1
  have hT1 : T ≠ ⊥ :=
    AS76b.isSylowOf_ne_bot_of_even hT (by rw [rightConjugate_card]; exact htight.1)
  have hTR' : Nat.card T = Nat.card R := by rw [hT.card_eq, hR.card_eq, rightConjugate_card]
  have hTNR : T ≤ normalizer (R : Set G) :=
    (commutator_eq_bot_iff_le_centralizer.1 hTR).trans (Subgroup.centralizer_le_normalizer _)
  have hTAK : T ≤ A ⊔ centralizer (A : Set G) :=
    AS76b.lemma33Two_of h32 h4 AS76b.asc08Lemma34 G A hA31 R hR g hg T
      (hT.of_le (le_inf hT.le hTN) inf_le_left) hT1 hTNR hT
  have hTe := AS76b.isElemAbelian_of_isSylowOf_rightConjugate h32 hA31 hT
  obtain ⟨t₀, ht₀, ht₀1⟩ := T.bot_or_exists_ne_one.resolve_left hT1
  obtain ⟨γ, l, w, hwA, hl, hγ, hwψ, hwodd, hwt₀, hTc⟩ :=
    exists_frame hA hψ hZ hm hK hKey hg hT.le hTN hTAK hTe ht₀ ht₀1
  have : IsSimpleGroup (leviA γ) := isSimpleGroup_leviA γ
  have hZS : center (leviA γ) = ⊥ := center_leviA exists_mul_ne_mul_SL2 γ
  have hL : CFSG.Open.IsQuasisimple (leviLift ψ (leviA γ)) :=
    isQuasisimple_leviLift hψ (leviA_le_innerP γ) (commutator_leviA γ) hZS
  have hLA := leviLift_le_inf_centralizer hψ hwA hwψ
  have hRT := not_le_normalizer hA hψ hZ hm hK hKey hg hT.le hTN hTAK hTe hR hR1 hRN ht₀ ht₀1
    hwA hl hγ hwψ hwodd hwt₀
  obtain ⟨hstd, hnn⟩ := AS76b.lemma38_of_noConj_of_le h4 h32 AS76b.asc08Lemma34 hA31 hR
    ((zpowers_le).2 hwA) hL hLA (normalizer_inf_centralizer_le hwA hwψ hl)
    (isSylowOf_inf_centralizer hψ hwA hwψ hl hA hR hR1)
    (le_sup_leviLift hψ hZ hTN hTAK hTe hTR hR hTc)
    (le_bot_iff.1 ((inf_le_inf_left T leviLift_le).trans
      (inf_eq_bot_of_le_rightConjugate (hKey g) hT.isPGroup hT.le).le))
    hTR' hRT
    (fun U hU hU1 c hle => not_conj_le_of_le hKey (hR.isPGroup.to_le hU) (hU.trans hR.le) hU1 c
      (hle.trans leviLift_le))
  have hLW : leviLift ψ (leviA γ) ≤ centralizer (zpowers w : Set G) := hLA.trans inf_le_right
  have hH' : RankTwoHyp (centralizer (zpowers w : Set G))
      ((leviLift ψ (leviA γ)).subgroupOf (centralizer (zpowers w : Set G))) :=
    ⟨kProper_subgroup (fun e h => CFSG.SectionRank.catalog_of_mulEquiv e h) hH.kProper _, hstd,
      hnn, two_le_pRank_centralizer_subgroupOf ((zpowers_le).2 hwA) leviLift_le hH.rank⟩
  obtain ⟨B, hB', hO', ⟨f⟩⟩ := exists_rankTwoHyp_quotient hH'
  let eL : rankTwoQuot ((leviLift ψ (leviA γ)).subgroupOf (centralizer (zpowers w : Set G))) ≃*
      SL2 K :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLW) (Subgroup.map_center_eq _)).trans
      ((leviLiftQuotEquiv hψ (leviA_le_innerP γ) (commutator_leviA γ) hZS).trans
        (leviAEquiv γ).symm)
  have hSz := (hB _ B hB' hO' (Or.inl ⟨m, hm,
    statedClassicalModel_of_mulEquiv_SL2 hm hK (f.symm.trans eL)⟩)).1
  apply not_three_dvd_card_of_suzukiModel_three hSz
  rw [Nat.card_congr (f.symm.trans eL).toEquiv]
  exact three_dvd_card_SL2

theorem l3_first_conjunct_of_foundation
    (h3 : AS76b.Section3Config) (h32 : AS76b.Lemma32) (h4 : AS76b.Asc75Theorem4)
    (hB : RankTwoBenderStandard) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHyp G A → ∀ m : ℕ, 2 ≤ m →
      Assembly.LowTwoRank.StatedClassicalModel (rankTwoQuot A) .PSL 3 2 m →
        standardComponentOddCore G = ⊥ → m = 2 := by
  intro G _ _ A hH m hm hQ hO
  by_contra hm2
  exact l3_part_one_of_foundation h3 h32 h4 hB G A hH m (by omega) hQ hO

end CFSG.ComponentClassification.RankTwoL3Even
