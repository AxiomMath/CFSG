module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GTriLab
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4Outer
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLeviToral
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusFrame
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.Cover
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.FamilyProved
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorDataCongr
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyFG
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.SeitzGeneration.Hyper
public import CFSG.LieType.SeitzGeneration.HyperBridge
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA3pSurvivor
public import CFSG.LocalAnalysis.AGLEmbedding.GapROneBS
public import CFSG.LocalAnalysis.AGLEmbedding.J3InSitu
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSide
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenAssembly
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3FourGenData
public import CFSG.LocalAnalysis.AGLEmbedding.MonomialWeightsOne
public import CFSG.LocalAnalysis.AGLEmbedding.ReeData
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTransfer
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Frontier3
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignCores
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLTorus
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.Census3.Assembly
public import CFSG.RankThree.PartOne.FOC.Cases
public import CFSG.RankThree.PartOne.FOC.CompEquiv
public import CFSG.RankThree.PartOne.FOC.PSLFamily
public import CFSG.RankThree.PartOne.FOC.PSLLie
public import CFSG.RankThree.PartOne.FOCD.G2OddQPlus
public import CFSG.RankThree.PartOne.FOCD.PRank
public import CFSG.RankThree.PartOne.KC.UnitaryDefining
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.N143.LowTwoRankSplit
public import CFSG.RankThree.PartOne.N143.SectionCenter
public import CFSG.RankThree.PartOne.N143.SectionRankBound
public import CFSG.RankThree.PartOne.N143.SectionRankProof
public import CFSG.RankThree.PartOne.N143.SectionRankSplit
public import CFSG.RankThree.PartOne.RF4.FinalSec66
public import CFSG.RankThree.PartOne.SEITZ11.G2OddFinal
public import CFSG.RankThree.PartOne.SEITZ7.D4Wire
public import CFSG.RankThree.PartOne.SEITZ7.SzPairK
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofSec19
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofSec4
public import CFSG.RankThree.PartTwo.Sec19.Step1914Split
public import CFSG.RankThree.PartTwo.Sec4.E27.FixReeF4
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzOther
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzRest
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RowsProofSeitzSz
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import Certificates.Certificate10050
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate17002
public import Certificates.Certificate17951
public import Certificates.Certificate8117
public import Certificates.Certificate8160

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GTri

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartTwo CFSG.PGLModel
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp

section Fix


theorem triFixModel {f : ℕ} (hf : 1 ≤ f) {K₃ : Type} [Field K₃] [Finite K₃]
    (hK₃ : Nat.card K₃ = (2 ^ f) ^ 3) (Fr : K₃ ≃+* K₃) (hFr : ∀ c, Fr c = c ^ (2 ^ f))
    (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range) :
    (∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = 2 ^ f ∧
      Nonempty (↥(fixSubgroup φ) ≃* ↥(adjointGroup Tag.G2 F₀))) ∨
    (∃ (F : Type) (_ : Field F) (π : Bool), Sec4.PiField π 2 f F ∧
      Nonempty (↥(fixSubgroup φ) ≃* ↥(projImage (Sec4.glPi π 3 (2 ^ f) F)))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hF : Nat.card (fixSubfield Fr) = 2 ^ f :=
    CFSG.GH74.GLS.Stage4.Hex.card_fixedField_of_cube Fr.toRingHom hq hK₃ hFr
  haveI : Finite (fixSubfield Fr) := Subtype.finite
  have hG2 : ↥(fixSubgroup (fieldActor (t := TwistTag.D4) Fr Fr)) ≃* ↥(adjointGroup Tag.G2 (fixSubfield Fr)) :=
    (nonempty_fixSubgroup_fieldActor_equiv_G2 (ℓ := 2) (by norm_num) hf (Or.inl rfl) hK₃ Fr hFr).some
  rcases Sec8.Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv hf hK₃ hFr hφ3 hφ with
    ⟨β, hβ | hβ⟩ | ⟨e₂⟩
  · rw [hβ]
    exact Or.inl ⟨fixSubfield Fr, inferInstance, inferInstance, hF,
      ⟨(fixSubgroupConjEquiv β _).symm.trans hG2⟩⟩
  · rw [hβ]
    exact Or.inl ⟨fixSubfield Fr, inferInstance, inferInstance, hF,
      ⟨((fixSubgroupConjEquiv β _).symm.trans
        (MulEquiv.subgroupCongr
          (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroup_inv_eq _))).trans hG2⟩⟩
  · have hfixφ : fixSubgroup φ = Sec4.autFix φ := Subgroup.ext fun _ => Iff.rfl
    let ef : ↥(fixSubgroup φ) ≃* ↥(Sec4.autFix φ) := MulEquiv.subgroupCongr hfixφ
    rcases Nat.even_or_odd f with hfe | hfo
    · obtain ⟨F, _, _, hF', ⟨e₃⟩⟩ := Sec8.kF82D4SecondCentY0Even_holds f hfe hf K₃ Fr hK₃ hFr
      exact Or.inr ⟨F, inferInstance, true, ⟨Nat.prime_two, hf, hF'⟩, ⟨ef.trans (e₂.some.trans e₃)⟩⟩
    · obtain ⟨F, _, _, hF', ⟨e₃⟩⟩ := Sec8.kF82D4SecondCentY0_holds f hfo K₃ Fr hK₃ hFr
      exact Or.inr ⟨F, inferInstance, false, ⟨Nat.prime_two, hf, hF'⟩, ⟨ef.trans (e₂.some.trans e₃)⟩⟩

theorem triOuter_canon_n (hRig : GGLabelRigidInput) {f : ℕ} (hf : 2 ≤ f) {K₃ : Type} [Field K₃]
    [Finite K₃] (hK₃ : Nat.card K₃ = (2 ^ f) ^ 3) (Fr : K₃ ≃+* K₃) (hFr : ∀ c, Fr c = c ^ (2 ^ f))
    (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range)
    {X : Type} [Group X] [Finite X] {C J : Subgroup X} (e : ↥C ≃* ↥(fixSubgroup φ))
    (hJ : GLAPComponent 3 C J) {labJ : GLALabel}
    (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ)) : (canonLabel labJ).n = f := by
  rcases triFixModel (by omega) hK₃ Fr hFr φ hφ3 hφ with
    ⟨F₀, _, _, hF₀, ⟨e'⟩⟩ | ⟨F, _, π, hF, ⟨e'⟩⟩
  · have := triCanon_G2 hRig hf hF₀ (e.trans e') hJ hlabJ
    rw [this]
  · cases π
    · exact triCanon_PGL_false hRig hf hF (e.trans e') hJ hlabJ
    · exact triCanon_PGL_true hRig hf hF (e.trans e') hJ hlabJ

end Fix

end CFSG.LocalAnalysis.GLTheoremA.Y10GTri
