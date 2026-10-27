module

public import CFSG.CGT.PushingUp.Inputs
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
import CFSG.RankThree.PartOne.S12.ModelTransport
import CFSG.StronglyEmbedded.Catalog.Suzuki
import CFSG.StronglyEmbedded.MatrixGroups.SzModel
import CFSG.Models.BenderSuzuki
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.S10.Defs
public import CFSG.StronglyEmbedded
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import Certificates.Certificate43

public section

namespace CFSG.CGT.PushingUp

open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.RankThree.PartOne (projSL_of_statedClassicalModel projSU_of_statedClassicalModel)

theorem benderBridge_psl {G : Type} [Group G] {n : ℕ} (hn : 2 ≤ n)
    (e : G ≃* CFSG.Theory.Comparator.PSL2Model n) :
    Nonempty (G ≃* projSL 2 (GaloisField 2 n)) := by
  have h4 : 4 ≤ 2 ^ n := (Nat.pow_le_pow_right (by norm_num) hn : 2 ^ 2 ≤ 2 ^ n)
  refine projSL_of_statedClassicalModel (n := 2) (f := n) ?_
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, GaloisField 2 n, inferInstance, inferInstance,
    GaloisField.card 2 n (by omega),
    ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField 2 n))⟩⟩
  · intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega
  · intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega

theorem benderBridge_psu {G : Type} [Group G] {n : ℕ} (hn : 2 ≤ n)
    (e : G ≃* CFSG.Theory.Comparator.PSU3Model n) :
    Nonempty (G ≃* projSU 3 2 n) := by
  have hmodel : CFSG.Theory.Comparator.PSU3Model n = CFSG.Open.PSU3 2 n :=
      CFSG.Models.benderPSU3Model_eq_psu3 n
  have h4 : 4 ≤ 2 ^ n := (Nat.pow_le_pow_right (by norm_num) hn : 2 ^ 2 ≤ 2 ^ n)
  have hcard : Nat.card (GaloisField 2 (2 * n)) = (2 ^ n) ^ 2 := by
    rw [GaloisField.card 2 (2 * n) (by omega), ← pow_mul, mul_comm]
  let e' : G ≃* StatedProj (StatedSU 3 (2 ^ n) (GaloisField 2 (2 * n))) :=
    (e.trans (MulEquiv.subgroupCongr hmodel)).trans
      (CFSG.ShultStronglyClosedTI.glaSUCanonicalEquivNative n).symm
  refine projSU_of_statedClassicalModel (n := 3) (f := n) ?_
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_⟩, GaloisField 2 (2 * n), inferInstance,
    inferInstance, hcard, ⟨e'⟩⟩
  intro h
  simp only [Prod.mk.injEq, true_and] at h
  omega

theorem benderBridge_suzuki {G : Type} [Group G] {n : ℕ} (hn : 1 ≤ n)
    (e : G ≃* CFSG.Theory.Comparator.SzModel n) :
    ∃ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid),
      Nonempty (G ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group) := by
  have hv : (TauCeti.LieTypeIndex.suzuki n).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simpa using hn
  exact ⟨n, hv, ⟨(e.trans (MulEquiv.subgroupCongr
    (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup n))).trans
    (CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv).symm⟩⟩

theorem benderModelsBridge :
    ∀ (G : Type) [Group G], CFSG.BenderSuzuki.IsBenderGroup G →
      (∃ n : ℕ, 1 ≤ n ∧ (Nonempty (G ≃* projSL 2 (GaloisField 2 n)) ∨
        Nonempty (G ≃* projSU 3 2 n))) ∨
      (∃ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid),
        Nonempty (G ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group)) := by
  intro G _ hG
  rcases hG with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · exact Or.inl ⟨n, by omega, Or.inl (benderBridge_psl hn e)⟩
  · exact Or.inr (benderBridge_suzuki hn e)
  · exact Or.inl ⟨n, by omega, Or.inr (benderBridge_psu hn e)⟩

end CFSG.CGT.PushingUp
