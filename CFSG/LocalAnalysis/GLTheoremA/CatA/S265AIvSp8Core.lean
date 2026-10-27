module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AIvSp8Dim
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AIvSp8Rad
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AIvSp8Fix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AIvSp8Trv
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Sp6
public import CFSG.LocalAnalysis.GLTheoremA.CatB.KFactsSp
public import CFSG.Assembly.LargeEvenGLABridge
public import CFSG.Assembly.OpenBridges
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.GroupTheory.PLayer.Bootstrap
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
public import CFSG.Holt.Fixed
public import CFSG.LargeExtraspecial.OfFStar
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Glue
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SpBlocks2
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Rank3
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4OutQuot
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.CatalogInputs
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1310a5b
public import CFSG.LocalAnalysis.GLTheoremB.Prop95Input18
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusEmbed
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueStep3Basic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallJ
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearEnd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryEnd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryPower
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Partner
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerSp
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Transfer
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaNormal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowUniqueStep
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Milestones.ASVolI.A2OddAut
public import CFSG.Milestones.ASVolI.F48.Core
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Thm
public import CFSG.RankThree.OddKernel.CompleteRankComparison
public import CFSG.RankThree.PartOne.KF.ClsPSL
public import CFSG.RankThree.PartOne.S11c.Sec66PSL
public import CFSG.RankThree.PartTwo.Sec11.Item1117ProofSwap
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofTools
public import CFSG.RankThree.PartTwo.Sec4.Item426A6
public import Certificates.Certificate41501
public import Certificates.Certificate8007
public import Certificates.Certificate8008

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine
open CFSG.RankThree.SubgroupLists (spForm spForm_isAlt spForm_nondegenerate)
open CFSG.RankThree.Classical (spEnd spEnd_apply)

theorem eq_bot_of_normalized_two_group_lin {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] {ψ : G →* (V ≃ₗ[ZMod 2] V)}
    {B : LinearMap.BilinForm (ZMod 2) V} (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hψ : Function.Injective ψ)
    (hrange : ∀ g : V ≃ₗ[ZMod 2] V, (∀ u v, B (g u) (g v) = B u v) → ∃ x, ψ x = g)
    (hiso : ∀ x u v, B (ψ x u) (ψ x v) = B u v) {Bb : Subgroup G} {d : G} (hd : d ∈ Bb)
    (hd3 : d ^ 3 = 1)
    (hdim : Nat.card ↥(LinearMap.ker ((ψ d : V →ₗ[ZMod 2] V) - 1)) * 4 = Nat.card V)
    (hC : ∀ W : Subgroup G, IsPGroup 2 W → W ≤ Subgroup.centralizer ({d} : Set G) →
      Bb ≤ Subgroup.normalizer (W : Set G) → W = ⊥)
    {W : Subgroup G} (hW : IsPGroup 2 W) (hBW : Bb ≤ Subgroup.normalizer (W : Set G)) :
    W = ⊥ := by
  by_contra hW1
  obtain ⟨I, hI0, hIiso, hIb⟩ := exists_isotropic_of_normalized_two_group hB hnd hψ hiso hW hBW hW1
  have hId : ∀ v ∈ I, ψ d v = v := fun v hv =>
    fixed_of_isotropic_pair hB hnd (hiso d) (by rw [← map_pow, hd3, map_one]) hdim
      (hIiso v hv _ (hIb d hd v hv))
  obtain ⟨W', hW'1, hW'2, hW'c, hW'n⟩ :=
    exists_centralized_two_group hB hnd hψ hrange hiso hI0 hIiso hIb hId
  exact hW'1 (hC W' hW'2 hW'c hW'n)

local notation "V₈" => Fin 4 ⊕ Fin 4 → ZMod 2

private noncomputable def sp8Act : StatedSp 4 (ZMod 2) →* (V₈ ≃ₗ[ZMod 2] V₈) :=
  (linIsometryGroup (spForm 4 (ZMod 2))).subtype.comp
    (statedSpEquivLinIsometryGroup 4 (ZMod 2)).toMonoidHom

private theorem sp8Act_coe (s : StatedSp 4 (ZMod 2)) :
    ((sp8Act s : V₈ ≃ₗ[ZMod 2] V₈) : V₈ →ₗ[ZMod 2] V₈) = spEnd s :=
  LinearMap.ext fun v => by
    rw [spEnd_apply]
    exact statedSpEquivLinIsometryGroup_apply 4 (ZMod 2) s v

private theorem sp8Act_injective : Function.Injective sp8Act :=
  (linIsometryGroup (spForm 4 (ZMod 2))).subtype_injective.comp
    (statedSpEquivLinIsometryGroup 4 (ZMod 2)).injective

private theorem sp8Act_isometry (s : StatedSp 4 (ZMod 2)) (u v : V₈) :
    spForm 4 (ZMod 2) (sp8Act s u) (sp8Act s v) = spForm 4 (ZMod 2) u v :=
  mem_linIsometryGroup.mp (statedSpEquivLinIsometryGroup 4 (ZMod 2) s).2 u v

theorem sp8_core {G : Type} [Group G] [Finite G] (hG : catalogIs G S8.L84.isSp82)
    {Bb : Subgroup G} {d : G} (hd : d ∈ Bb) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hcard : 1451520 ≤ Nat.card ↥(Subgroup.centralizer ({d} : Set G)))
    (hC : ∀ W : Subgroup G, IsPGroup 2 W → W ≤ Subgroup.centralizer ({d} : Set G) →
      Bb ≤ Subgroup.normalizer (W : Set G) → W = ⊥)
    {W : Subgroup G} (hW : IsPGroup 2 W) (hBW : Bb ≤ Subgroup.normalizer (W : Set G)) :
    W = ⊥ := by
  obtain ⟨e⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.KFacts.bridge_sp8two hG
  let ψ : G →* (V₈ ≃ₗ[ZMod 2] V₈) := sp8Act.comp e.toMonoidHom
  have hed3 : (e d) ^ 3 = 1 := by rw [← map_pow, hd3, map_one]
  have hed1 : e d ≠ 1 := fun h => hd1 (e.injective (h.trans (map_one e).symm))
  have hle : (Subgroup.centralizer ({d} : Set G)).map e.toMonoidHom ≤
      Subgroup.centralizer ({e d} : Set (StatedSp 4 (ZMod 2))) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    simpa using congrArg e (Subgroup.mem_centralizer_iff.mp hx d rfl)
  have hcard' : 1451520 ≤ Nat.card ↥(Subgroup.centralizer ({e d} : Set (StatedSp 4 (ZMod 2)))) :=
    calc 1451520 ≤ Nat.card ↥(Subgroup.centralizer ({d} : Set G)) := hcard
      _ = Nat.card ↥((Subgroup.centralizer ({d} : Set G)).map e.toMonoidHom) :=
        (Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).symm
      _ ≤ _ := Subgroup.card_le_of_le hle
  have h6 := finrank_ker_eq_six_of_card hed3 hed1 hcard'
  have h8 : Module.finrank (ZMod 2) V₈ = 8 := by
    simp [Module.finrank_fintype_fun_eq_card]
  have hk : Nat.card ↥(LinearMap.ker (spEnd (e d) - 1)) = 64 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, h6]
    norm_num
  have hV : Nat.card V₈ = 256 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, h8]
    norm_num
  refine eq_bot_of_normalized_two_group_lin (ψ := ψ) spForm_isAlt spForm_nondegenerate
    (sp8Act_injective.comp e.injective) (fun g hg => ?_) (fun x u v => sp8Act_isometry (e x) u v)
    hd hd3 ?_ hC hW hBW
  · obtain ⟨s, hs⟩ := (statedSpEquivLinIsometryGroup 4 (ZMod 2)).surjective
      ⟨g, mem_linIsometryGroup.mpr hg⟩
    exact ⟨e.symm s, by simpa [ψ, sp8Act] using congrArg Subtype.val hs⟩
  · show Nat.card ↥(LinearMap.ker (((sp8Act (e d) : V₈ ≃ₗ[ZMod 2] V₈) :
      V₈ →ₗ[ZMod 2] V₈) - 1)) * 4 = _
    rw [sp8Act_coe, hk, hV]

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
