module

public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Basic
public import CFSG.Blueprint.Catalog
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
import CFSG.StronglyEmbedded.BenderUnitaryBorel
import CFSG.StronglyEmbedded.BenderBorelTransport
import CFSG.Adapters.LinearFieldTransport
import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
import CFSG.LieType.BorelTits.Suzuki
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
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
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem noNonsolvableClassical_of_psl_two {X : Type} [Group X] {f : ℕ} (hf : 2 ≤ f)
    (h : StatedClassicalModel X .PSL 2 2 f) : NoNonsolvableClassical X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e' := e.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 2 2 f (by omega) hK)
  have : Finite PSL(2, GaloisField 2 f) := Finite.of_surjective
    (QuotientGroup.mk : SL(2, GaloisField 2 f) → PSL(2, GaloisField 2 f))
    QuotientGroup.mk_surjective
  exact NoNonsolvableClassical.of_mulEquiv e'
    (NoNonsolvableClassical.of_fusionBenderBorel (bender_psl2_borel_full f hf))

theorem noNonsolvableClassical_of_psu_three {X : Type} [Group X] {f : ℕ} (hf : 2 ≤ f)
    (h : StatedClassicalModel X .PSU 3 2 f) : NoNonsolvableClassical X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hcard : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  let e' : X ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K (2 ^ f)) := e
  have e'' := e'.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative f hf hcard)
  have hX : Finite X := Finite.of_equiv
    (CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K (2 ^ f))) e'.symm.toEquiv
  have : Finite (PSU3 2 f) := Finite.of_equiv X e''.toEquiv
  exact NoNonsolvableClassical.of_mulEquiv e''
    (NoNonsolvableClassical.of_fusionBenderBorel (bender_psu3_borel_full f hf))

theorem noNonsolvableClassical_of_suzukiModel {X : Type} [Group X] {f : ℕ}
    (h : CFSG.Blueprint.SuzukiModel X 2 f) : NoNonsolvableClassical X := by
  obtain ⟨-, a, ha, K, _, _, rfl, hcard, ⟨e⟩⟩ := h
  have e' := e.trans ((MulEquiv.subgroupCongr
    (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
    (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard))
  have hX : Finite X := Finite.of_equiv ↥(CFSG.Blueprint.suzukiGroup a K) e.symm.toEquiv
  have : Finite (Sz a) := Finite.of_equiv X e'.toEquiv
  exact NoNonsolvableClassical.of_mulEquiv e'
    (NoNonsolvableClassical.of_fusionBenderBorel (bender_suzuki_borel_full a ha))

end CFSG.ClassicalInvolution
