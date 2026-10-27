module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureCases
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieTools
import CFSG.RankThree.PartTwo.Sec19.Step1915WProofLie3K
import CFSG.Adapters.RankTwoModelTransports
import CFSG.Open.PGLModelStated
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate9124
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials
import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
import CFSG.LocalAnalysis.AGLEmbedding.Extremal
import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.RankThree.PartOne.CTP.StrongPSylow
import CFSG.RankThree.PartTwo.Sec15.HypR
import CFSG.RankThree.PartTwo.Sec19.Item194Used
import CFSG.RankThree.PartTwo.Sec19.Step1915W
import CFSG.RankThree.PartTwo.Sec19.Step1917ProofDefs
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import Certificates.Certificate2201

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

private theorem wcC3_normalizerMovesLines_of_fusion {K : Type} [Group K] [Finite K] {p : ℕ}
    [Fact p.Prime] {P : Subgroup K}
    (h : ∀ x ∈ P, x ≠ 1 →
      ∃ g ∈ Subgroup.normalizer (P : Set K), g * x * g⁻¹ ∉ Subgroup.zpowers x) :
    NormalizerMovesLines p P := by
  intro A hAP hA
  obtain ⟨x, hxA, hx1⟩ : ∃ x ∈ A, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : A = ⊥ := (Subgroup.eq_bot_iff_forall A).2 hcon
    rw [this, Subgroup.card_bot] at hA
    exact (Fact.out : p.Prime).one_lt.ne hA
  have hord : orderOf x = p := by
    have h1 : orderOf x ∣ Nat.card A := Subgroup.orderOf_dvd_natCard A hxA
    rw [hA] at h1
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 h1 with h2 | h2
    · exact absurd (orderOf_eq_one_iff.1 h2) hx1
    · exact h2
  have heq : Subgroup.zpowers x = A := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxA)
    rw [hA, Nat.card_zpowers, hord]
  obtain ⟨g, hg, hgx⟩ := h x (hAP hxA) hx1
  refine ⟨g, hg, fun hmap => hgx ?_⟩
  rw [heq]
  have hmem : g * x * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom :=
    ⟨x, hxA, by simp [MulAut.conj_apply]⟩
  rwa [hmap] at hmem

private theorem wcC3_wcOn_three {K : Type} [Group K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    (hf : 1 ≤ f) (hiso : CFSG.RankThree.PartTwo.Sec4.IsoLThreePi K ℓ f)
    (h91 : ℓ ^ f % 9 ≠ 1) (h98 : ℓ ^ f % 9 ≠ 8) : WCOn 3 K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P₀⟩ : Nonempty (Sylow 3 K) := inferInstance
  refine WCOn.of_normalizerMovesLines P₀ fun _ _ => ?_
  exact wcC3_normalizerMovesLines_of_fusion fun x hx hx1 =>
    CFSG.RankThree.PartTwo.Sec19.Step1915WProof.ks1917Lie3Fusion K ℓ f hf hiso h91 h98 P₀ x hx hx1

private theorem wcC3_nonempty_mulEquiv_projSL {K : Type} [Group K] {ℓ f : ℕ} [Fact ℓ.Prime]
    (h : CFSG.Open.StatedClassicalModel K .PSL 3 ℓ f) :
    Nonempty (K ≃* CFSG.PGLModel.projSL 3 (GaloisField ℓ f)) := by
  obtain ⟨hadm, F, _, _, hF, ⟨e⟩⟩ := h
  have hf : f ≠ 0 := by
    have := hadm.2.1
    omega
  let _ : Fintype F := Fintype.ofFinite F
  let _ : Fintype (GaloisField ℓ f) := Fintype.ofFinite _
  have hcard : Fintype.card F = Fintype.card (GaloisField ℓ f) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, GaloisField.card ℓ f hf]
  let φ : F ≃+* GaloisField ℓ f := FiniteField.ringEquivOfCardEq hcard
  exact ⟨e.trans ((CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin 3) φ)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSL φ 3)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)).trans
    (CFSG.PGLModel.projSLEquivStatedProj 3 (GaloisField ℓ f)).symm)⟩

private theorem wcC3_nonempty_mulEquiv_projSU {K : Type} [Group K] {ℓ f : ℕ} [Fact ℓ.Prime]
    (h : CFSG.Open.StatedClassicalModel K .PSU 3 ℓ f) :
    Nonempty (K ≃* CFSG.PGLModel.projSU 3 ℓ f) := by
  obtain ⟨hadm, F, _, _, hF, ⟨e⟩⟩ := h
  have hf : f ≠ 0 := by
    have := hadm.2.1
    omega
  let _ : Fintype F := Fintype.ofFinite F
  let _ : Fintype (GaloisField ℓ (2 * f)) := Fintype.ofFinite _
  have hcard : Fintype.card F = Fintype.card (GaloisField ℓ (2 * f)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
      GaloisField.card ℓ (2 * f) (by omega), ← pow_mul, mul_comm]
  let φ : F ≃+* GaloisField ℓ (2 * f) := FiniteField.ringEquivOfCardEq hcard
  exact ⟨e.trans ((CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin 3) φ)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU φ 3 (ℓ ^ f))
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)).trans
    (CFSG.PGLModel.projSUEquivStatedProj 3 ℓ f).symm)⟩

theorem wcOn_cross_psl_three {K : Type} [Group K] [Finite K] {ℓ f : ℕ}
    (h : CFSG.Open.StatedClassicalModel K .PSL 3 ℓ f) (hq : ℓ ^ f % 9 = 4 ∨ ℓ ^ f % 9 = 7) :
    WCOn 3 K := by
  haveI : Fact ℓ.Prime := ⟨h.1.1⟩
  obtain ⟨e⟩ := wcC3_nonempty_mulEquiv_projSL h
  have hiso : CFSG.RankThree.PartTwo.Sec4.IsoLThreePi K ℓ f := Or.inl ⟨by omega, ⟨e⟩⟩
  exact wcC3_wcOn_three h.1.2.1 hiso (by omega) (by omega)

theorem wcOn_cross_psu_three {K : Type} [Group K] [Finite K] {ℓ f : ℕ}
    (h : CFSG.Open.StatedClassicalModel K .PSU 3 ℓ f) (hq : ℓ ^ f % 9 = 2 ∨ ℓ ^ f % 9 = 5) :
    WCOn 3 K := by
  haveI : Fact ℓ.Prime := ⟨h.1.1⟩
  obtain ⟨e⟩ := wcC3_nonempty_mulEquiv_projSU h
  have hiso : CFSG.RankThree.PartTwo.Sec4.IsoLThreePi K ℓ f := Or.inr ⟨by omega, ⟨e⟩⟩
  exact wcC3_wcOn_three h.1.2.1 hiso (by omega) (by omega)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
