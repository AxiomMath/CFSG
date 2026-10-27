module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentStepFiveFive
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentStepFiveOne
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentStepFiveTwo
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableNormalCyclic
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsMisc5
import CFSG.Adapters.QiuzhenLegacy.FeitThompson.Gorenstein.RelativeZJ
import CFSG.Certificates.CentralKernel
import CFSG.Certificates.CosetTableWalkC
import CFSG.Certificates.FusionF2
import CFSG.Certificates.WordSubgroupHom
import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
import CFSG.HardMathSupport.Solomon.Coordinator.I28_8Defs
import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
import CFSG.HardMathSupport.Solomon.LocalBalance.Prop42CaseThreeProof
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6Interface
import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Setup
import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
import CFSG.LargeExtraspecial.OrthoF2
import CFSG.LargeExtraspecial.S2Basic
import CFSG.LargeExtraspecial.S5Defs
import CFSG.LieType.Chevalley.EvenRootCommutatorF4
import CFSG.LieType.SteinbergBROddSylowCore
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Containment
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
import CFSG.LocalAnalysis.GL83PartI.I713.Extension
import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
import CFSG.LocalAnalysis.GLTheoremB.Connected
import CFSG.LocalAnalysis.GLTheoremB.Lemma99Core
import CFSG.LocalAnalysis.GLTheoremB.Prop95Input18
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorOrbit
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionIndexTwoStrongEmbedding
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
import CFSG.Quasithin.Background.B15P4LayerDict
import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.Sporadic.Presentation.Co2Base
import CFSG.Sporadic.Presentation.Co2Cover
import CFSG.Sporadic.Presentation.Co2Fusion
import CFSG.Sporadic.Presentation.Co2FusionInputs
import CFSG.Sporadic.Presentation.McLExactData
import CFSG.Sporadic.Presentation.McLExactInputs
import CFSG.Sporadic.Schreier.J1QT
import CFSG.Sporadic.Schreier.TitsOther
import CFSG.YGroups.DCE.B433Check
import Certificates.Certificate9124

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.HallHigman (IsPSolvable)
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal
  (isPSolvable_of_mulEquiv)

section PSolvable

variable {p : ℕ} [Fact p.Prime]

theorem isPSolvable_of_isSolvable' {X : Type*} [Group X] [Finite X] (h : Group.IsSolvable X) :
    IsPSolvable p X :=
  haveI := h
  CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.isPSolvable_of_normal_coprime_quotient_solvable ⊥
    (by rw [Subgroup.card_bot]; exact Nat.coprime_one_right p)
    (Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective ⊥))

theorem isPSolvable_of_hasNormalPComplement {X : Type*} [Group X] [Finite X]
    (h : CFSG.HasNormalPComplement p X) : IsPSolvable p X := by
  obtain ⟨N, hN, hc, hq⟩ := h
  haveI := hq.isNilpotent
  exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.isPSolvable_of_normal_coprime_quotient_solvable
    N hc inferInstance

theorem isPSolvable_of_surjective {X W : Type} [Group X] [Group W] [Finite X] (f : X →* W)
    (hf : Function.Surjective f) (h : IsPSolvable p X) : IsPSolvable p W := by
  have h1 : IsPSolvable p ↥(⊤ : Subgroup X) :=
    isPSolvable_of_mulEquiv Subgroup.topEquiv.symm h
  have h2 := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_map f h1
  rw [Subgroup.map_top_of_surjective f hf] at h2
  exact isPSolvable_of_mulEquiv Subgroup.topEquiv h2

theorem hasNormalPComplement_of_subsingleton {X : Type*} [Group X] [Subsingleton X] :
    CFSG.HasNormalPComplement p X :=
  ⟨⊤, inferInstance, by rw [Subgroup.card_top, Nat.card_unique]; exact Nat.coprime_one_right p,
    fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

end PSolvable

variable {G : Type} [Group G] [Finite G]

section Generic

variable {p : ℕ} [Fact p.Prime] {C : Subgroup G}
  {K : Subgroup (C ⧸ primeComplementCore (G := C) p)} [hK : K.Normal]

local notation "φ" => RankOneSylow.act (primeComplementCore (G := C) p) K

theorem hasNormalPComplement_d1PlusCore (hp2 : p ≠ 2)
    (hXr : Open.pRank p (d1PlusCore p C K) ≤ 1) {b : G} (hbC : b ∈ C)
    (hb : ∀ c ∈ C, b * c = c * b) (hbo : orderOf b = p) :
    CFSG.HasNormalPComplement p ↥(d1PlusCore p C K) := by
  have hXC : d1PlusCore p C K ≤ C := Subgroup.map_subtype_le _
  have hbot : ((d1PlusCore p C K).subgroupOf C).map φ = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_bot.mpr
      (MonoidHom.mem_ker.mp ((mem_d1PlusCore_iff_mem_ker x).mp (Subgroup.mem_subgroupOf.mp hx)))
  refine hasNormalPComplement_of_act hp2 hXr hbC hb hbo hXC ?_
  rw [hbot]
  haveI : Subsingleton ↥(⊥ : Subgroup (MulAut ↥K)) :=
    ⟨fun a b => Subtype.ext ((Subgroup.mem_bot.mp a.2).trans (Subgroup.mem_bot.mp b.2).symm)⟩
  exact hasNormalPComplement_of_subsingleton

theorem isPSolvable_inf_of (hI4 : KFactStepThreeMaximal) (hI6 : KFactStepThreeNormSolv)
    {P : Sylow p G} {M : Subgroup G} (hcore : GLBWeakCore p (P : Subgroup G) ≤ M) (hp2 : p ≠ 2)
    (hZ : Subgroup.center ↥K = ⊥) (hK1 : 1 ≤ Open.pRank p (⊤ : Subgroup ↥K))
    (hSt : StepThreeGroup p ↥K) (hA : IsEmpty (↥K ≃* alternatingGroup (Fin 10)))
    (hKX : ¬ K ≤ d1X0 p M C)
    (hXM : d1PlusCore p C K ≤ M) (hXr : Open.pRank p (d1PlusCore p C K) ≤ 1)
    {B E : Subgroup G} {b : G} (hBC : CFSG.ABGLocalTools.IsSylowOf p B C) (hBM : B ≤ M)
    (hbB : b ∈ B) (hb : ∀ c ∈ C, b * c = c * b) (hbo : orderOf b = p)
    (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) (hEB : E ≤ B) :
    IsPSolvable p ↥(C ⊓ M) := by
  have hmem := mem_iff_act_mem_normalizer hI4 hcore hp2 hZ hK1 hSt hA hKX hXM hXr hBC hBM hbB
    hb hbo hE hEc hEB
  set S : Subgroup (MulAut ↥K) := ((B ⊓ hyp111Pre p C K).subgroupOf C).map φ with hS
  set g : ↥(C ⊓ M) →* MulAut ↥K := MonoidHom.comp φ (Subgroup.inclusion inf_le_left) with hg
  have hX := hasNormalPComplement_d1PlusCore hp2 hXr (hBC.le hbB) hb hbo
  have hker : IsPSolvable p ↥g.ker := by
    let f : ↥g.ker →* ↥(d1PlusCore p C K) :=
      { toFun := fun y => ⟨((y : ↥(C ⊓ M)) : G), (mem_d1PlusCore_iff_mem_ker
          (Subgroup.inclusion inf_le_left (y : ↥(C ⊓ M)))).mpr (MonoidHom.mem_ker.mpr
            (MonoidHom.mem_ker.mp y.2))⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := fun a b hab => by
      have h := congrArg (fun z : ↥(d1PlusCore p C K) => (z : G)) hab
      exact Subtype.ext (Subtype.ext h)
    exact isPSolvable_of_hasNormalPComplement
      (CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc5.hasNormalPComplement_of_injective
        f hf hX)
  have hNs : Group.IsSolvable ↥(Subgroup.normalizer (S : Set (MulAut ↥K))) :=
    hI6 p (MulAut ↥K) _ S conj_range_normal (centralizer_conj_range_eq_bot hZ)
      (stepThreeGroup_conj_range hZ hSt) (isSylowOf_act hZ hBC)
  have hrange : g.range ≤ Subgroup.normalizer (S : Set (MulAut ↥K)) := by
    rintro _ ⟨c, rfl⟩
    exact (hmem (Subgroup.inclusion inf_le_left c)).mp c.2.2
  have hRs : Group.IsSolvable ↥g.range :=
    haveI := hNs
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hrange)
  have hQs : Group.IsSolvable (↥(C ⊓ M) ⧸ g.ker) :=
    haveI := hRs
    Group.isSolvable_of_isSolvable_injective (QuotientGroup.quotientKerEquivRange g).injective
  exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_normal
    g.ker hker (isPSolvable_of_isSolvable' hQs)

theorem isPSolvable_quot_of (hI4 : KFactStepThreeMaximal) (hI6 : KFactStepThreeNormSolv)
    {P : Sylow p G} {M : Subgroup G} (hcore : GLBWeakCore p (P : Subgroup G) ≤ M) (hp2 : p ≠ 2)
    (hZ : Subgroup.center ↥K = ⊥) (hK1 : 1 ≤ Open.pRank p (⊤ : Subgroup ↥K))
    (hSt : StepThreeGroup p ↥K) (hA : IsEmpty (↥K ≃* alternatingGroup (Fin 10)))
    (hKX : ¬ K ≤ d1X0 p M C)
    (hXM : d1PlusCore p C K ≤ M) (hXr : Open.pRank p (d1PlusCore p C K) ≤ 1)
    {B E : Subgroup G} {b : G} (hBC : CFSG.ABGLocalTools.IsSylowOf p B C) (hBM : B ≤ M)
    (hbB : b ∈ B) (hb : ∀ c ∈ C, b * c = c * b) (hbo : orderOf b = p)
    (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) (hEB : E ≤ B)
    (hC : ∀ x : G, b * x = x * b → x ∈ C) {J : Subgroup G} (hJM : J ≤ M)
    (hbJ : b ∈ Subgroup.normalizer (J : Set G))
    (hbJ2 : ∀ x ∈ J, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 J) :
    IsPSolvable p (↥J ⧸ CFSG.pCore 2 ↥J) := by
  have hCM := isPSolvable_inf_of hI4 hI6 hcore hp2 hZ hK1 hSt hA hKX hXM hXr hBC hBM hbB hb hbo
    hE hEc hEB
  have hCJ : IsPSolvable p ↥(C ⊓ J) :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le hCM
      (inf_le_inf_left C hJM)
  have hbk : b ^ (p ^ 1) = 1 := by rw [pow_one, ← hbo]; exact pow_orderOf_eq_one b
  exact isPSolvable_of_surjective _ (surjective_inf_quot hp2 hbk hbJ hbJ2 hC) hCJ

end Generic

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
