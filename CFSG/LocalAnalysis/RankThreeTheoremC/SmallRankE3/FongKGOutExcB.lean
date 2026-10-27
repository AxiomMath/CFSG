module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongKGOutGen
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Catalog
public import CFSG.Adapters.ExceptionalCatalogReverse
public import CFSG.Sporadic.Schreier.TitsOuterTwo
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
public import CFSG.StronglyEmbedded.Catalog.Suzuki
public import CFSG.RankThree.PartTwo.Sec21.Item224KFactsProofRed
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import Mathlib.FieldTheory.Finite.GaloisField
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyStatements
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.RankThree.PartTwo.Sec21.Item22Statements
public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongOut

open TauCeti CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof

theorem outTwoCyclic_suzuki
    (m : ℕ) (hv : (LieTypeIndex.suzuki m).Valid) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* (CFSGIndex.lie ⟨.suzuki m, hv⟩).Group) : OutTwoCyclic Y := by
  have hm : 1 ≤ m := by
    have h := ((LieTypeIndex.valid_iff _).1 hv).1
    simpa [LieTypeIndex.inStandardRange_iff] using h
  have hK : Nat.card (GaloisField 2 (2 * m + 1)) = 2 ^ (2 * m + 1) :=
    GaloisField.card 2 (2 * m + 1) (by omega)
  have hmodel : CFSG.Blueprint.SuzukiModel Y 2 (2 * m + 1) :=
    ⟨rfl, m, hm, GaloisField 2 (2 * m + 1), inferInstance, inferInstance, rfl, hK,
      ⟨e.trans ((CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK).trans
        (CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv).symm).symm⟩⟩
  exact outTwoCyclic_of_outPNice_two
    (CFSG.RankThree.PartOne.OutStructure.outPNice_Suzuki Nat.prime_two hmodel)

theorem outTwoCyclic_reeF4
    (m : ℕ) (hv : (LieTypeIndex.reeF4 m).Valid) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* (CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group) : OutTwoCyclic Y := by
  have hm : 1 ≤ m := by
    have h := ((LieTypeIndex.valid_iff _).1 hv).1
    simpa [LieTypeIndex.inStandardRange_iff] using h
  have hK : Nat.card (GaloisField 2 (2 * m + 1)) = 2 ^ (2 * m + 1) :=
    GaloisField.card 2 (2 * m + 1) (by omega)
  have hhalf : (ReeF4LieIndex.of m hv).toSuzukiReeIndex.halfExponent = m :=
    SuzukiReeIndex.halfExponent_reeF4 m hv
  have hcard : Nat.card (GaloisField 2 (2 * m + 1)) =
      2 ^ (2 * (ReeF4LieIndex.of m hv).toSuzukiReeIndex.halfExponent + 1) := by
    rw [hhalf]
    exact hK
  obtain ⟨e₁⟩ := CFSG.TauCetiBridge.reeF4_candidate_equiv_of_card (ReeF4LieIndex.of m hv) hcard
  rw [hhalf] at e₁
  have hadm : CFSG.Open.StatedLieAdmissible .twistedF4 0 2 (2 * m + 1) := by
    unfold CFSG.Open.StatedLieAdmissible
    exact ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩
  have hmodel : CFSG.Blueprint.ReeTitsModel Y .twistedF4 2 (2 * m + 1) :=
    ⟨hadm, m, rfl, GaloisField 2 (2 * m + 1), inferInstance, inferInstance, hK,
      ⟨e.trans (e₁.trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv
        (K := GaloisField 2 (2 * m + 1)) m).symm)⟩⟩
  exact outTwoCyclic_of_outPNice_two
    (CFSG.RankThree.PartOne.OutStructure.outPNice_twistedF4 Nat.prime_two hmodel)

theorem outTwoCyclic_tits
    (hv : LieTypeIndex.tits.Valid) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* (CFSGIndex.lie ⟨.tits, hv⟩).Group) : OutTwoCyclic Y := by
  have hK : Nat.card (GaloisField 2 1) = 2 ^ 1 := GaloisField.card 2 1 one_ne_zero
  have hK2 : Nat.card (GaloisField 2 1) = 2 := hK.trans (by norm_num)
  obtain ⟨e₁⟩ := CFSG.TauCetiBridge.tits_candidate_equiv_of_card TitsLieIndex.of hK2
  have hmodel : CFSG.Blueprint.ReeTitsModel Y .Tits 2 1 :=
    ⟨⟨Nat.prime_two, le_refl 1, rfl, rfl, rfl⟩, 0, by norm_num, GaloisField 2 1,
      inferInstance, inferInstance, hK,
      ⟨e.trans (e₁.trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv
        (K := GaloisField 2 1) 0).symm)⟩⟩
  have hO : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y) = 2 :=
    (CFSG.Sporadic.Schreier.Tits.CTI_Tits_model_outer_two_part_bound Y 2 1 hmodel).2.2.1
  exact outTwoCyclic_of_not_four_dvd_card_outer (by rw [hO]; norm_num)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongOut

end
