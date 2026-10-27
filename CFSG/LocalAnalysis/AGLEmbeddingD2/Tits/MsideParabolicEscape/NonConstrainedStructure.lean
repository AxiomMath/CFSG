module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.NonConstrainedBranch
public import CFSG.Open.StatedDefs
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreStar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThree
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallResidues
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltThreeRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwoTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ScalarTorus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Survivor
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ThreeStrong
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
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
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerParab3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Sub3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathShortMap
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLargeHolds
public import CFSG.Quasithin.Background.GoldschmidtAmalgamPairCentral
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S141Statements
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S145Basic
public import CFSG.Quasithin.EmptyFaithful.S146Defs
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartOne.S8.Statements
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.QuasithinUnique
open scoped Pointwise

@[expose] def IsRankTwoLayerType (Y : Type) [Group Y] : Prop :=
  Nonempty (Y ≃* alternatingGroup (Fin 6)) ∨ StatedClassicalModel Y .PSL 3 2 1 ∨
    StatedClassicalModel Y .PSU 3 3 1

instance glbPrimeCore_subgroupOf_normal {G : Type} [Group G] [Finite G] (M : Subgroup G) :
    ((GLBPrimeCore 3 M).subgroupOf M).Normal where
  conj_mem x hx g := by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hg := le_normalizer_glbPrimeCore 3 M g.2
    exact (Subgroup.mem_normalizer_iff.mp hg x.1).mp hx

@[expose] def starImg {G : Type} [Group G] [Finite G] (M Y : Subgroup G) :
    Subgroup (M ⧸ (GLBPrimeCore 3 M).subgroupOf M) :=
  (Y.subgroupOf M).map (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M))

@[expose] def IsRankTwoLayer {G : Type} [Group G] [Finite G] (M L : Subgroup G) : Prop :=
  L ≤ M ∧ GLBPrimeCore 3 M ≤ L ∧ (L.subgroupOf M).Normal ∧ IsSimpleGroup ↥(starImg M L) ∧
    ¬ IsMulCommutative ↥(starImg M L) ∧ IsRankTwoLayerType ↥(starImg M L)

@[expose] def D2L34BetaTwoLocalSylow : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    GLBStronglyEmbedded 3 M → D2L34AllResidue P M → D2L34Kmax H →
    ∀ T : Subgroup G, IsSylowTwoOf T M → ∀ N : Subgroup G, IsTwoLocal N → T ≤ N →
      ¬ CFSG.HallHigman.IsPSolvable 3 ↥(N ⊓ M) → IsSylowTwoOf T N

@[expose] def D2L34BetaNormalizerSolvable : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    GLBStronglyEmbedded 3 M → D2L34AllResidue P M → D2L34Kmax H →
    ∀ T : Subgroup G, IsSylowTwoOf T M → ∀ C : Subgroup G, C ≠ ⊥ → C ≤ T →
      (C.subgroupOf T).Characteristic →
      CFSG.HallHigman.IsPSolvable 3 ↥(Subgroup.normalizer (C : Set G) ⊓ M)

@[expose] def D2L34BetaLayerExists : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    GLBStronglyEmbedded 3 M → D2L34AllResidue P M → D2L34Kmax H →
    ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥M →
    ∃ L : Subgroup G, IsRankTwoLayer M L

@[expose] def D2L34BetaLayerCentralized : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    GLBStronglyEmbedded 3 M → D2L34AllResidue P M → D2L34Kmax H →
    ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥M →
    ∀ L : Subgroup G, IsRankTwoLayer M L →
      ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ GLBPrimeCore 3 M

@[expose] def D2L34BetaLayerPermutable : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    GLBStronglyEmbedded 3 M → D2L34AllResidue P M → D2L34Kmax H →
    ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥M →
    ∀ U : Subgroup G, IsBetaBase H M U → A ≤ Subgroup.normalizer (U : Set G) →
      Subgroup.normalizer (U : Set G) ≤ H →
      IsSylowTwoOf (U ⊓ GLBPrimeCore 3 M) (GLBPrimeCore 3 M) →
      IsSylowTwoOf U (GLBPrimeCore 3 (H ⊓ M)) →
      ∀ L : Subgroup G, IsRankTwoLayer M L →
        ∃ P₁ : Subgroup G, P₁ ≤ L ∧ Nat.card P₁ = 3 ∧ (P₁ : Set G) * U = U * P₁

theorem glbPrimeCore_subgroupOf_normal_of_le {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hLM : L ≤ M) : ((GLBPrimeCore 3 M).subgroupOf L).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  have hg := le_normalizer_glbPrimeCore 3 M (hLM g.2)
  simpa using (Subgroup.mem_normalizer_iff.mp hg x.1).mp hx

noncomputable def quotientEquivStarImg {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hLM : L ≤ M) [((GLBPrimeCore 3 M).subgroupOf L).Normal] :
    (L ⧸ (GLBPrimeCore 3 M).subgroupOf L) ≃* ↥(starImg M L) := by
  set f : ↥L →* M ⧸ (GLBPrimeCore 3 M).subgroupOf M :=
    (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M)).comp (Subgroup.inclusion hLM) with hf
  have hker : f.ker = (GLBPrimeCore 3 M).subgroupOf L := by
    ext x
    simp [hf, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hrange : f.range = starImg M L := by
    ext y
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨Subgroup.inclusion hLM l, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m.1, Subgroup.mem_subgroupOf.mp hm⟩, rfl⟩
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange))

theorem simpleNonabelianModulo_of_isRankTwoLayer {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (h : IsRankTwoLayer M L) : SimpleNonabelianModulo L (GLBPrimeCore 3 M) := by
  obtain ⟨hLM, -, -, hs, hnc, -⟩ := h
  have hn := glbPrimeCore_subgroupOf_normal_of_le hLM
  have := hn
  refine ⟨hn, ?_, ?_⟩
  · exact MulEquiv.isSimpleGroup (quotientEquivStarImg hLM)
  · intro hc
    apply hnc
    refine ⟨⟨fun a b => ?_⟩⟩
    have := hc.is_comm.comm ((quotientEquivStarImg hLM).symm a) ((quotientEquivStarImg hLM).symm b)
    have h2 := congrArg (quotientEquivStarImg hLM) this
    simpa using h2

theorem nonConstrainedInput_of_structure (hL : D2L34BetaLayerExists)
    (hC : D2L34BetaLayerCentralized) (hP : D2L34BetaLayerPermutable) :
    D2L34BetaMSideNonConstrainedInput := by
  intro d G _ _ P M A H R Rbar K hc hstr hAll hKmax hcon U hU hAU hNHU hsylU hUQ
  obtain ⟨L, hlay⟩ := hL d G P M A H R Rbar K hc hstr hAll hKmax hcon
  obtain ⟨P₁, hP₁L, hP₁c, hperm⟩ :=
    hP d G P M A H R Rbar K hc hstr hAll hKmax hcon U hU hAU hNHU hsylU hUQ L hlay
  exact ⟨P₁, L, hlay.1, hlay.2.2.1, hP₁L, hP₁c, hperm,
    hC d G P M A H R Rbar K hc hstr hAll hKmax hcon L hlay,
    simpleNonabelianModulo_of_isRankTwoLayer hlay⟩

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
