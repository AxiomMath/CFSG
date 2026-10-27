module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Indices
public import CFSG.Open.StatedDefs
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorOmega
import CFSG.Adapters.LinearCatalog
import CFSG.Adapters.LinearFieldTransport
import CFSG.Blueprint.Catalog
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.ClassicalGroups.Orthogonal.Simple
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LieType.Universal.Unitary.Clause0
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOrthLow
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitAction
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointIsometryRegular
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageCases
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageSplit
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.Open.StatedSUFieldChange
import CFSG.RankThree.PartOne.K1214.SylowSL2
import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusModel
import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusSix
import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
import CFSG.RankThree.PartOne.KC.OrthogonalRegularCoverage
import CFSG.RankThree.PartOne.S11d.OrthModels
import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.SectionRank.SignLines
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LieType.Ree.LargeReeEightTorus
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOrthLowB
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentCore
import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentDisplayed
import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentTags
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.RankThree.PartOne.S12.InputsSec15
import CFSG.RankThree.PartOne.S12.Sec15FA
import CFSG.RankThree.PartOne.S12.Sec15Items
import CFSG.RankThree.PartOne.S15K.FixedWitt
import CFSG.RankThree.PartOne.S15K.LayerModel
import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
import CFSG.RankThree.Theta.ThreeComponentOrbitCover
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
import Certificates.Certificate10
import Certificates.Certificate11
import Certificates.Certificate12
import Certificates.Certificate3
import Certificates.Certificate4
import Certificates.Certificate42
import Certificates.Certificate44
import Certificates.Certificate5
import Certificates.Certificate6
import Certificates.Certificate7
import Certificates.Certificate8
import Certificates.Certificate9
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthFix

open QuadraticMap CFSG.RankThree.Classical2 CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

@[expose] def OrthFixedIdx (n : ℕ) : TauCeti.LieTypeIndex → Prop
  | .D s q => (IsTwoPow q 1 ∨ IsTwoPow q 3) ∧ Even s ∧ 4 ≤ s ∧ s < n
  | .twistedD s q => (IsTwoPow q 1 ∨ IsTwoPow q 3) ∧ Odd s ∧ 5 ≤ s ∧ s < n
  | .twistedA r q => (IsTwoPow q 1 ∨ IsTwoPow q 3) ∧ r = 3 ∧ 3 < n
  | .A r q => r = 1 ∧ IsTwoPow q 3
  | _ => False

theorem exists_lie_A_one {E : Type} [Field E] [Finite E] (hE : Nat.card E = 8) (n : ℕ) :
    ∃ i : TauCeti.ValidLieTypeIndex, OrthFixedIdx n i.1 ∧
      Nonempty ((Matrix.SpecialLinearGroup (Fin 2) E ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E)) ≃*
          (TauCeti.CFSGIndex.lie i).Group) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q : TauCeti.PrimePower := ⟨2, 3, Nat.prime_two, by norm_num⟩
  have hv : (TauCeti.LieTypeIndex.A 1 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp [q, TauCeti.PrimePower.card_def]
  let eF := CFSG.ClassicalModels.finiteFieldEquivGaloisField E 2 3 (by norm_num)
    (by rw [hE]; norm_num)
  let eP := CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv eF (Fin 2)
  let eC := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv
  exact ⟨⟨.A 1 q, hv⟩, ⟨rfl, rfl, rfl⟩, ⟨eP.trans eC.symm⟩⟩

theorem exists_lie_twistedA_three {E : Type} [Field E] [Finite E] {k n : ℕ}
    (hE : Nat.card E = (2 ^ k) ^ 2) (hk : k = 1 ∨ k = 3) (hn : 3 < n) :
    ∃ i : TauCeti.ValidLieTypeIndex, OrthFixedIdx n i.1 ∧
      Nonempty ((↥(CFSG.Open.StatedSU 4 (2 ^ k) E) ⧸
        Subgroup.center ↥(CFSG.Open.StatedSU 4 (2 ^ k) E)) ≃*
          (TauCeti.CFSGIndex.lie i).Group) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk0 : 0 < k := by omega
  have hmq : ((4 : ℕ), 2 ^ k) ≠ (3, 2) := by
    intro hh
    have := congrArg Prod.fst hh
    simp at this
  have hQ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) hE
    (by norm_num) hmq
  let q : TauCeti.PrimePower := ⟨2, k, Nat.prime_two, hk0⟩
  have hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff]
    refine ⟨?_, by simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]⟩
    rw [TauCeti.LieTypeIndex.inStandardRange_iff]
    exact ⟨by norm_num, fun hr => absurd hr (by norm_num)⟩
  obtain ⟨-, K₀, _, _, hK₀, ⟨e₀⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv (MulEquiv.refl _)
  haveI : Fintype K₀ := Fintype.ofFinite _
  haveI : Fintype E := Fintype.ofFinite E
  have hKK : Fintype.card E = Fintype.card K₀ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK₀, hE]
  let eK : E ≃+* K₀ := FiniteField.ringEquivOfCardEq hKK
  let eP := CFSG.Open.StatedSUFieldChange.statedProjSUEquiv eK (3 + 1) (2 ^ k)
  let eC := QuotientGroup.quotientMulEquivOfEq hQ.2
  refine ⟨⟨.twistedA 3 q, hv⟩, ⟨?_, rfl, hn⟩, ⟨(eC.trans eP).trans e₀.symm⟩⟩
  rcases hk with rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

theorem exists_lie_D_of_model {G : Type} [Group G] {s f n : ℕ}
    (hG : CFSG.Open.StatedClassicalModel G .POmegaPlus s 2 f) (hf : f = 1 ∨ f = 3)
    (hs : Even s) (hsn : s < n) :
    ∃ i : TauCeti.ValidLieTypeIndex, OrthFixedIdx n i.1 ∧
      Nonempty (G ≃* (TauCeti.CFSGIndex.lie i).Group) := by
  have h4 : 4 ≤ s := hG.1.2.2
  have hf0 : 0 < f := by omega
  let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, hf0⟩
  have hv : (TauCeti.LieTypeIndex.D s q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨h4, fun h => h⟩
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hG
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD s q hv (MulEquiv.refl _))
  refine ⟨⟨.D s q, hv⟩, ⟨?_, hs, h4, hsn⟩, ⟨e⟩⟩
  rcases hf with rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

theorem exists_lie_twistedD_of_model {G : Type} [Group G] {s f n : ℕ}
    (hG : CFSG.Open.StatedClassicalModel G .POmegaMinus s 2 f) (hf : f = 1 ∨ f = 3)
    (hs : Odd s) (h5 : 5 ≤ s) (hsn : s < n) :
    ∃ i : TauCeti.ValidLieTypeIndex, OrthFixedIdx n i.1 ∧
      Nonempty (G ≃* (TauCeti.CFSGIndex.lie i).Group) := by
  have h4 : 4 ≤ s := hG.1.2.2
  have hf0 : 0 < f := by omega
  let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, hf0⟩
  have hv : (TauCeti.LieTypeIndex.twistedD s q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨h4, fun h => h⟩
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hG
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD s q hv (MulEquiv.refl _))
  refine ⟨⟨.twistedD s q, hv⟩, ⟨?_, hs, h5, hsn⟩, ⟨e⟩⟩
  rcases hf with rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

private abbrev FixNQ (n : ℕ) (G : Type) [Group G] : Prop :=
  (∀ N : Subgroup G, N.Normal → CFSG.IsQuasisimple ↥N →
      Subgroup.center ↥N = ⊥ ∧ ∃ i : TauCeti.ValidLieTypeIndex, OrthFixedIdx n i.1 ∧
        Nonempty ((↥N ⧸ Subgroup.center ↥N) ≃* (TauCeti.CFSGIndex.lie i).Group)) ∧
    ∃ N₁ N₂ : Subgroup G, ∀ N : Subgroup G, N.Normal → CFSG.IsQuasisimple ↥N → N = N₁ ∨ N = N₂

private abbrev FixData (n : ℕ) (G : Type) [Group G] : Prop :=
  CFSG.IsQuasisimple G ∧ Subgroup.center G = ⊥ ∧ ∃ i : TauCeti.ValidLieTypeIndex,
    OrthFixedIdx n i.1 ∧ Nonempty ((G ⧸ Subgroup.center G) ≃* (TauCeti.CFSGIndex.lie i).Group)

private theorem nq_of_false {n : ℕ} {G : Type} [Group G]
    (h : ∀ N : Subgroup G, N.Normal → ¬ CFSG.IsQuasisimple ↥N) : FixNQ n G :=
  ⟨fun N hN hNq => (h N hN hNq).elim, ⊥, ⊥, fun N hN hNq => (h N hN hNq).elim⟩

private theorem nq_of_data {n : ℕ} {G : Type} [Group G] (h : FixData n G) : FixNQ n G := by
  obtain ⟨hq, hZ, i, hi, ⟨e⟩⟩ := h
  have htop : ∀ N : Subgroup G, N.Normal → CFSG.IsQuasisimple ↥N → N = ⊤ := fun N hN hNq =>
    Solomon.Coordinator.LieComp.OmegaAux.eq_top_of_isQuasisimple hq hN hNq
  refine ⟨fun N hN hNq => ?_, ⊤, ⊤, fun N hN hNq => Or.inl (htop N hN hNq)⟩
  obtain rfl := htop N hN hNq
  refine ⟨?_, i, hi, ⟨(QuotientGroup.congr _ _ Subgroup.topEquiv
    (Subgroup.map_center_eq _)).trans e⟩⟩
  rw [eq_bot_iff]
  intro x hx
  have hxG : (x : G) ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun g =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hx ⟨g, Subgroup.mem_top g⟩)
  rw [hZ, Subgroup.mem_bot] at hxG
  exact Subgroup.mem_bot.2 (Subtype.ext hxG)

private theorem center_eq_bot_of_simple {G : Type} [Group G] [IsSimpleGroup G]
    (hq : CFSG.IsQuasisimple G) : Subgroup.center G = ⊥ := by
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G)).resolve_right
    fun h => ?_
  obtain ⟨-, -, a, b, hab⟩ := hq
  have h1 : ∀ z : G ⧸ Subgroup.center G, z = 1 := fun z => by
    induction z using QuotientGroup.induction_on with
    | H x => exact (QuotientGroup.eq_one_iff x).2 (by rw [h]; exact Subgroup.mem_top x)
  exact hab (by rw [h1 a, h1 b])

section Cases

variable {F : Type} [Field F] [Finite F] [CharP F 2] {W : Type} [AddCommGroup W] [Module F W]
  [FiniteDimensional F W] {R : QuadraticForm F W}

private theorem exp_cases {f : ℕ} (hF : Nat.card F = 2 ∨ Nat.card F = 8)
    (hcard : Nat.card F = 2 ^ f) : f = 1 ∨ f = 3 := by
  rcases hF with h | h
  · exact Or.inl (Nat.pow_right_injective le_rfl
      (show 2 ^ f = 2 ^ 1 from hcard.symm.trans (h.trans (by norm_num))))
  · exact Or.inr (Nat.pow_right_injective le_rfl
      (show 2 ^ f = 2 ^ 3 from hcard.symm.trans (h.trans (by norm_num))))

private theorem sl_two_part (hF8 : Nat.card F = 8) (n : ℕ) {N : Type} [Group N]
    (ψ : Matrix.SpecialLinearGroup (Fin 2) F ≃* N) :
    Subgroup.center N = ⊥ ∧ ∃ i : TauCeti.ValidLieTypeIndex, OrthFixedIdx n i.1 ∧
      Nonempty ((N ⧸ Subgroup.center N) ≃* (TauCeti.CFSGIndex.lie i).Group) := by
  refine ⟨?_, ?_⟩
  · rw [← Subgroup.map_center_eq ψ, CFSG.RankThree.PartOne.K1214.center_SL2_eq_bot,
      Subgroup.map_bot]
  · obtain ⟨i, hi, ⟨eL⟩⟩ := exists_lie_A_one hF8 n
    exact ⟨i, hi, ⟨(QuotientGroup.congr _ _ ψ.symm (Subgroup.map_center_eq _)).trans eL⟩⟩

open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
  CFSG.LocalAnalysis.ComponentInitial in
private theorem nq_four_eight (hF8 : Nat.card F = 8) (hR : (polarBilin R).Nondegenerate)
    (hd : Module.finrank F W = 4)
    (hS : ∃ S : Submodule F W, Module.finrank F S = 2 ∧ ∀ x ∈ S, R x = 0) (n : ℕ) :
    FixNQ n ↥(orthDerived R) := by
  classical
  haveI : Finite W := Module.finite_of_finite F
  haveI : Finite (W ≃ₗ[F] W) := Finite.of_injective (fun e : W ≃ₗ[F] W => (e : W → W))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨-, e, -, -, hsup, hq₁, hq₂, hn₁, hn₂, -, -, -⟩ :=
    orthogonal_split_four_derived (by omega) (by omega) R hR hd hS
  have hcases : ∀ N : Subgroup ↥(orthDerived R), N.Normal → CFSG.IsQuasisimple ↥N →
      N.map (Solomon.Coordinator.LieComp.OmegaAux.ιO R) =
          (determinantLeftFactor F).map e.symm.toMonoidHom ∨
        N.map (Solomon.Coordinator.LieComp.OmegaAux.ιO R) =
          (determinantRightFactor F).map e.symm.toMonoidHom := by
    intro N hN hNq
    haveI := hN
    have hMD : N.map (Solomon.Coordinator.LieComp.OmegaAux.ιO R) ≤
        commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
      rw [← Solomon.Coordinator.LieComp.OmegaAux.range_ιO]
      exact Subgroup.map_le_range _ _
    exact CFSG.ComponentClassification.CatLeafProof.eq_or_eq_of_isComponent_le_sup hsup hq₁
      hq₂ hn₁ hn₂ (Solomon.Coordinator.LieComp.OmegaAux.isComponent_map_ιO R hNq) hMD
  have hsl : ∀ φ : Matrix.SpecialLinearGroup (Fin 2) F →* DeterminantIsometries F,
      Function.Injective φ → ∀ N : Subgroup ↥(orthDerived R),
        N.map (Solomon.Coordinator.LieComp.OmegaAux.ιO R) = φ.range.map e.symm.toMonoidHom →
          Nonempty (Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥N) := fun φ hφ N h =>
    ⟨(MonoidHom.ofInjective hφ).trans ((φ.range.equivMapOfInjective e.symm.toMonoidHom
      e.symm.injective).trans ((MulEquiv.subgroupCongr h).symm.trans
        (N.equivMapOfInjective _ (Solomon.Coordinator.LieComp.OmegaAux.ιO_injective R)).symm))⟩
  have hinl : Function.Injective ((specialRho (K := F)).comp (MonoidHom.inl _ _)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro A hA
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.inl_apply,
      specialRho_eq_one_iff] at hA
    obtain ⟨c, -, h1, h2⟩ := hA
    exact Subgroup.mem_bot.2 (Matrix.SpecialLinearGroup.toGL_injective (h1.trans h2.symm))
  have hinr : Function.Injective ((specialRho (K := F)).comp (MonoidHom.inr _ _)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro A hA
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.inr_apply,
      specialRho_eq_one_iff] at hA
    obtain ⟨c, -, h1, h2⟩ := hA
    exact Subgroup.mem_bot.2 (Matrix.SpecialLinearGroup.toGL_injective (h2.trans h1.symm))
  refine ⟨fun N hN hNq => ?_, ((determinantLeftFactor F).map e.symm.toMonoidHom).comap
    (Solomon.Coordinator.LieComp.OmegaAux.ιO R), ((determinantRightFactor F).map
      e.symm.toMonoidHom).comap (Solomon.Coordinator.LieComp.OmegaAux.ιO R),
    fun N hN hNq => ?_⟩
  · obtain ⟨ψ⟩ : Nonempty (Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥N) :=
      (hcases N hN hNq).elim (hsl _ hinl N) (hsl _ hinr N)
    exact sl_two_part hF8 n ψ
  · rcases hcases N hN hNq with h | h
    · exact Or.inl (by rw [← h, Subgroup.comap_map_eq_self_of_injective
        (Solomon.Coordinator.LieComp.OmegaAux.ιO_injective R)])
    · exact Or.inr (by rw [← h, Subgroup.comap_map_eq_self_of_injective
        (Solomon.Coordinator.LieComp.OmegaAux.ιO_injective R)])

private theorem six_minus (hF : Nat.card F = 2 ∨ Nat.card F = 8)
    (hR : (polarBilin R).Nondegenerate) (hd : Module.finrank F W = 6)
    (hno : ¬ ∃ T : Submodule F W, Module.finrank F T = 3 ∧ ∀ x ∈ T, R x = 0) {n : ℕ}
    (hn : 3 < n) : FixData n ↥(orthDerived R) := by
  have hts : ∀ U : Submodule F W, Module.finrank F U = 3 → ∃ u ∈ U, R u ≠ 0 := by
    intro U hU
    by_contra hcon
    push Not at hcon
    exact hno ⟨U, hU, hcon⟩
  obtain ⟨E, _, _, D, ψ, hψ⟩ :=
    CFSG.RankThree.PartOne.KCOrthogonal.exists_evenMinus_model R hR (n := 3) (by norm_num)
      (by omega) hts
  haveI : CharP E 2 := CFSG.RankThree.PartOne.KCOrthogonal.charP_two_of_algebra (K := F)
  haveI := D.finite_E
  let e1 : R.IsometryEquiv (CFSG.RankThree.PartOne.KCOrthogonal.evenNormTailForm D.N 2) :=
    { toLinearEquiv := ψ
      map_app' := fun w => hψ w }
  let e2 : R.IsometryEquiv D.sixForm := e1.trans D.sixIsometry
  obtain ⟨-, -, -, -, -, -, -, -, hinj, -, -, -, -, -, -, -, hcomm, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_six_unitary_derived_model D
  have hrange : orthDerived D.sixForm = D.sixRho.range := hcomm
  let e3 : D.sixSU ≃* ↥(orthDerived D.sixForm) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange.symm)
  obtain ⟨f, hU, hcard, hbar⟩ := D.exists_unitaryFieldData
  obtain ⟨e4⟩ := D.nonempty_sixSU_mulEquiv hU hbar
  let e5 : CFSG.Open.StatedSU 4 (2 ^ f) E ≃* ↥(orthDerived R) :=
    e4.symm.trans (e3.trans (CFSG.RankThree.PartOne.orthDerivedEquiv e2).symm)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNat : Nat.card E = (2 ^ f) ^ 2 := by rw [D.card_E, hcard]
  have hnq : ((4 : ℕ), 2 ^ f) ≠ (3, 2) := by
    intro hh
    have := congrArg Prod.fst hh
    simp at this
  have hSq := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hNat
    (by norm_num) hnq).1
  haveI := (CFSG.RankThree.PartOne.KCOrthogonal.statedSU_four_char_two_perfect_simple hU).2
  haveI : IsSimpleGroup ↥(orthDerived R) := e5.symm.isSimpleGroup
  have hq : CFSG.IsQuasisimple ↥(orthDerived R) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e5 hSq
  obtain ⟨i, hi, ⟨eL⟩⟩ := exists_lie_twistedA_three hNat (exp_cases hF hcard) hn
  exact ⟨hq, center_eq_bot_of_simple hq, i, hi,
    ⟨(QuotientGroup.congr _ _ e5.symm (Subgroup.map_center_eq _)).trans eL⟩⟩

open CFSG.GroupTheory.WeirSylow CFSG.LieType.Universal.Spin
  CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry in
private theorem large (hF : Nat.card F = 2 ∨ Nat.card F = 8)
    (hR : (polarBilin R).Nondegenerate) {s : ℕ} (hs : Module.finrank F W = 2 * s) (h4 : 4 ≤ s)
    (htype : IsPlusType R ↔ Even s) : FixData (s + 1) ↥(orthDerived R) := by
  haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := F) (M := W) (by omega)
  obtain ⟨f, hf, hcard⟩ : ∃ f, (f = 1 ∨ f = 3) ∧ Nat.card F = 2 ^ f :=
    hF.elim (fun h => ⟨1, Or.inl rfl, h.trans (by norm_num)⟩)
      fun h => ⟨3, Or.inr rfl, h.trans (by norm_num)⟩
  by_cases hev : Even s
  · obtain ⟨e⟩ := nonempty_isometry_quadPlus hR hs (htype.2 hev)
    have hT := singular_three_isometry e.symm
      (CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := F) (n := s) (by omega)).2
    have hZ := CFSG.RankThree.PartOne.center_orthDerived_eq_bot hR hT
    obtain ⟨i, hi, ⟨eL⟩⟩ := exists_lie_D_of_model
      ((CFSG.RankThree.PartOne.lieModel_of_orthDerived_plus (m := s) h4 (by omega) hcard e
        (MulEquiv.refl _)).statedClassicalModel (by decide)) hf hev (Nat.lt_succ_self s)
    exact ⟨CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hR hT, hZ, i, hi,
      ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans eL⟩⟩
  · have hodd : Odd s := Nat.not_even_iff_odd.1 hev
    have h5 : 5 ≤ s := by
      obtain ⟨k, hk⟩ := hodd
      omega
    rcases exists_isometry_quadPlus_or_quadMinus R hR (by omega : 1 ≤ s) hs with
      he | ⟨b, c, hirr, ⟨e⟩⟩
    · obtain ⟨e⟩ := he
      exact absurd (htype.1 ((isPlusType_congr e).2 (isPlusType_quadPlus F s))) hev
    · have hT := singular_three_isometry e.symm
        (CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (n := s) h4 hirr).2
      have hZ := CFSG.RankThree.PartOne.center_orthDerived_eq_bot hR hT
      obtain ⟨i, hi, ⟨eL⟩⟩ := exists_lie_twistedD_of_model
        ((CFSG.RankThree.PartOne.lieModel_of_orthDerived_minus (m := s) h4 (by omega) hcard
          hirr e (MulEquiv.refl _)).statedClassicalModel (by decide)) hf hodd h5
        (Nat.lt_succ_self s)
      exact ⟨CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hR hT, hZ, i, hi,
        ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans eL⟩⟩

private theorem big_data (hF : Nat.card F = 2 ∨ Nat.card F = 8)
    (hR : (polarBilin R).Nondegenerate) {s : ℕ} (hs : Module.finrank F W = 2 * s)
    (htype : 1 ≤ s → (CFSG.GroupTheory.WeirSylow.IsPlusType R ↔ Even s)) (hs3 : 3 ≤ s) :
    FixData (s + 1) ↥(orthDerived R) := by
  rcases (show s = 3 ∨ 4 ≤ s by omega) with rfl | h4
  · exact six_minus hF hR (by omega)
      (fun ⟨T, hT3, hTs⟩ => absurd ((htype (by norm_num)).1 ⟨T, by omega, hTs⟩) (by decide))
      (by norm_num)
  · exact large hF hR hs h4 (htype (by omega))

end Cases

theorem orthDerived_not_quasisimple_le_two {F : Type} [Field F] [Finite F] [CharP F 2]
    {W : Type} [AddCommGroup W] [Module F W] [FiniteDimensional F W] {R : QuadraticForm F W}
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) {s : ℕ} (hs : Module.finrank F W = 2 * s)
    (h1 : s ≤ 1) :
    ∀ N : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived R), N.Normal →
      ¬ CFSG.IsQuasisimple ↥N := by
  have : Fintype F := Fintype.ofFinite F
  exact fun N _ hNq => Solomon.Coordinator.LieComp.OmegaAux.M.case_le_two hR (by omega) N hNq

theorem orthDerived_not_quasisimple_small {F : Type} [Field F] [Finite F] [CharP F 2]
    {W : Type} [AddCommGroup W] [Module F W] [FiniteDimensional F W] {R : QuadraticForm F W}
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) {s : ℕ} (hs : Module.finrank F W = 2 * s)
    (htype : 1 ≤ s → (CFSG.GroupTheory.WeirSylow.IsPlusType R ↔ Even s))
    (hsmall : s ≤ 1 ∨ (s = 2 ∧ Nat.card F = 2)) :
    ∀ N : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived R), N.Normal →
      ¬ CFSG.IsQuasisimple ↥N := by
  intro N hN hNq
  haveI : Fintype F := Fintype.ofFinite F
  rcases hsmall with h1 | ⟨rfl, h2⟩
  · exact Solomon.Coordinator.LieComp.OmegaAux.M.case_le_two hR (by omega) N hNq
  · haveI := hN
    obtain ⟨S, hS, hSs⟩ := (htype (by norm_num)).2 (by decide)
    haveI :=
      Solomon.Coordinator.LieComp.OmegaAux.A.isSolvable_orthogonalGroup_of_smallFixedException
        R hR (by omega) (Or.inr ⟨⟨by omega, S, by omega, hSs⟩, Or.inl h2⟩)
    exact CFSG.ComponentClassification.CatLeafProof.not_isComponent_of_isSolvable
      (Solomon.Coordinator.LieComp.OmegaAux.isComponent_map_ιO R hNq)

theorem orthDerived_quasisimple_normal_eq_top_of_minus_four {F : Type} [Field F] [Finite F]
    [CharP F 2] {W : Type} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {R : QuadraticForm F W}
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) (hdim : Module.finrank F W = 4)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType R) :
    ∀ N : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived R), N.Normal →
      CFSG.IsQuasisimple ↥N → N = ⊤ := by
  intro N hN hNq
  have hts : ∀ U : Submodule F W, Module.finrank F U = Module.finrank F W / 2 →
      ∃ u ∈ U, R u ≠ 0 := by
    intro U hU
    by_contra hcon
    push Not at hcon
    exact hminus ⟨U, by rw [hU, hdim], hcon⟩
  have : IsSimpleGroup ↥(CFSG.RankThree.Classical2.orthDerived R) :=
    (CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction R hR
      (Or.inl hdim) hts).1
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exfalso
    have htriv : ∀ x : ↥N, (x : ↥(CFSG.RankThree.Classical2.orthDerived R)) = 1 := fun x =>
      (Subgroup.eq_bot_iff_forall (H := N)).mp h x.1 x.2
    obtain ⟨a, b, hab⟩ := hNq.2.1.exists_pair_ne
    obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥N) a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥N) b
    refine hab ?_
    rw [show a' = b' from Subtype.ext ((htriv a').trans (htriv b').symm)]
  · exact h

theorem orthDerived_quasisimple_normal {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ∨ Nat.card F = 8) {W : Type} [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] {R : QuadraticForm F W}
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) {s : ℕ} (hs : Module.finrank F W = 2 * s)
    (htype : 1 ≤ s → (CFSG.GroupTheory.WeirSylow.IsPlusType R ↔ Even s)) :
    (∀ N : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived R), N.Normal → CFSG.IsQuasisimple ↥N →
      Subgroup.center ↥N = ⊥ ∧ ∃ i : TauCeti.ValidLieTypeIndex, OrthFixedIdx (s + 1) i.1 ∧
        Nonempty ((↥N ⧸ Subgroup.center ↥N) ≃* (TauCeti.CFSGIndex.lie i).Group)) ∧
    ∃ N₁ N₂ : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived R),
      ∀ N : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived R),
        N.Normal → CFSG.IsQuasisimple ↥N → N = N₁ ∨ N = N₂ := by
  rcases Nat.lt_or_ge s 3 with h3 | h3
  · rcases (show s ≤ 1 ∨ s = 2 by omega) with h1 | rfl
    · exact nq_of_false (orthDerived_not_quasisimple_small hR hs htype (Or.inl h1))
    · obtain ⟨S, hS, hSs⟩ := (htype (by norm_num)).2 (by decide)
      rcases hF with h2 | h8
      · exact nq_of_false (orthDerived_not_quasisimple_small hR hs htype (Or.inr ⟨rfl, h2⟩))
      · exact nq_four_eight h8 hR (by omega) ⟨S, by omega, hSs⟩ _
  · exact nq_of_data (big_data hF hR hs htype h3)

end CFSG.HardMathSupport.Dickson.Bal207.OrthFix

end
