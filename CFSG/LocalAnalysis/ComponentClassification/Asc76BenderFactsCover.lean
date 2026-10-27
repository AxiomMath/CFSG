module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFactsAut
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CoversExclusion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CoversSuzuki
public import Certificates.Certificate113
import CFSG.Models.BenderSuzuki
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitary
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BenderGroupFactsUnitary
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open

theorem commutator_eq_top_of_center_eq_bot {G : Type*} [Group G] [IsSimpleGroup G]
    (h : center G = ⊥) : commutator G = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with hc | hc
  · rw [commutator_eq_bot_iff_center_eq_top, h] at hc
    exact absurd hc bot_ne_top
  · exact hc

variable {Y : Type} [Group Y] [Finite Y] {Z : Subgroup Y} [Z.Normal]

theorem commutator_eq_top_of_le_commutator (hB : fusionIsBenderGroup (Y ⧸ Z))
    (hcen : center (Y ⧸ Z) = ⊥) (hle : Z ≤ commutator Y) : commutator Y = ⊤ := by
  have : IsSimpleGroup (Y ⧸ Z) :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  have hmap : (commutator Y).map (QuotientGroup.mk' Z) = commutator (Y ⧸ Z) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective Z),
      commutator_def]
  rw [eq_top_iff]
  intro y _
  have hy : (y : Y ⧸ Z) ∈ (commutator Y).map (QuotientGroup.mk' Z) := by
    rw [hmap, commutator_eq_top_of_center_eq_bot hcen]
    exact mem_top _
  obtain ⟨c, hc, hcy⟩ := hy
  have hcZ : c⁻¹ * y ∈ Z := QuotientGroup.eq.mp hcy
  simpa using mul_mem hc (hle hcZ)

theorem center_eq_of_le_commutator (hZc : Z ≤ center Y) (hB : fusionIsBenderGroup (Y ⧸ Z))
    (hcen : center (Y ⧸ Z) = ⊥) (hle : Z ≤ commutator Y) :
    commutator Y = ⊤ ∧ center Y = Z := by
  have hperf := commutator_eq_top_of_le_commutator hB hcen hle
  exact ⟨hperf,
    CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCover.center_eq_of_fusionIsBenderGroup hZc
      hperf hB⟩

theorem not_le_commutator_of_mulEquiv_psu3 (hZc : Z ≤ center Y) (hZ2 : Nat.card Z = 2)
    {f : ℕ} (hf : 2 ≤ f) (e : Y ⧸ Z ≃* PSU3 2 f) : ¬ Z ≤ commutator Y := by
  intro hle
  obtain ⟨hperf, hcenter⟩ := center_eq_of_le_commutator hZc (Or.inr (Or.inl ⟨f, hf, ⟨e⟩⟩))
    (center_eq_bot_of_mulEquiv_psu3 hf e) hle
  have : Group.IsPerfect Y := ⟨hperf⟩
  have hp : IsPGroup 2 (center Y) := by
    rw [hcenter]
    exact IsPGroup.of_card (n := 1) (by rw [hZ2, pow_one])
  have hbot := CFSG.QuasithinUnique.RankOneRecog.unitary_center_eq_bot hp hf
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans e)
  rw [hcenter] at hbot
  rw [hbot, Subgroup.card_bot] at hZ2
  omega

theorem eq_one_of_le_commutator_of_mulEquiv_sz (hZc : Z ≤ center Y) (hZ2 : Nat.card Z = 2)
    {a : ℕ} (ha : 1 ≤ a) (e : Y ⧸ Z ≃* Sz a) (hle : Z ≤ commutator Y) : a = 1 := by
  by_contra ha1
  obtain ⟨hperf, hcenter⟩ := center_eq_of_le_commutator hZc (Or.inr (Or.inr ⟨a, ha, ⟨e⟩⟩))
    (center_eq_bot_of_mulEquiv_sz ha e) hle
  have hZ2' : Nat.card (center Y) = 2 := by rw [hcenter, hZ2]
  let e' : Y ⧸ center Y ≃* Sz a := (QuotientGroup.quotientMulEquivOfEq hcenter).trans e
  have hmodel : CFSG.Theory.Comparator.SzModel a = Sz a := CFSG.Models.benderSzModel_eq_sz a
  obtain ⟨Q⟩ : Nonempty (Sylow 2 Y) := inferInstance
  let Qb : Sylow 2 (Y ⧸ center Y) := Q.mapSurjective (QuotientGroup.mk'_surjective (center Y))
  have hBF := CFSG.ProperTwoGeneratedCore.TheoremC.benderBorelFactsHold _
    (isBenderGroup_of_mulEquiv_sz ha e') Qb
  rw [Sylow.coe_mapSurjective] at hBF
  have hCF := CFSG.ProperTwoGeneratedCore.Lemma37.benderCoverFacts_sylow_of_mulEquiv
    (e'.trans (MulEquiv.subgroupCongr hmodel.symm))
    (CFSG.ProperTwoGeneratedCore.Lemma37.suzukiCoverFacts (by omega)) Qb
  rw [Sylow.coe_mapSurjective] at hCF
  exact CFSG.ProperTwoGeneratedCore.Lemma37.CoverExclusion.false_of_benderCoverFacts hperf hZ2' Q
    hBF hCF

end CFSG.ComponentClassification.Asc76X
