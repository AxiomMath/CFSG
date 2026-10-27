module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Sp6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Blocks6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcDefs
public import CFSG.Assembly.LargeEvenGLABridge
public import CFSG.Assembly.OpenBridges
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.GroupTheory.PLayer.Bootstrap
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerSimple
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Glue
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SpBlocks2
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
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusEmbed
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsGeneration
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueStep3Basic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallJ
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLiftAniso
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR7iii
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotWeakCT
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
public import Certificates.Certificate41501

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
open CFSG.RankThree.PartOne.KCOrthogonal (exists_coe_add_of_isCompl)
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

namespace SpEngine

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] {p : ℕ}

theorem fixedByEnd_blockEnd_eq_ker (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (D : Hyperplane A p) :
    fixedByEnd (blockEnd A hp hpF hA t ht D) =
      LinearMap.ker (projBlock A hp hpF hA D) := by
  refine le_antisymm ?_ ?_
  · intro v hv
    rw [mem_fixedByEnd] at hv
    obtain ⟨u, r, -, rfl⟩ :=
      exists_coe_add_of_isCompl (isCompl_blockSpace_ker A hp hpF hA D) v
    have hr : (r : V) ∈ LinearMap.ker (projBlock A hp hpF hA D) := by
      rw [LinearMap.mem_ker]; exact r.2
    rw [map_add, blockEnd_apply_mem A hp hpF hA t ht D u.2,
      blockEnd_apply_of_ker A hp hpF hA t ht D hr] at hv
    have h2 : (t D : V ≃ₗ[F] V) (u : V) = (u : V) := add_right_cancel hv
    have h3 : (u : V) = 0 := eq_zero_of_fixed_mem_blockSpace A hp hpF hA (ht D) u.2 h2
    rw [LinearMap.mem_ker, h3]
    simp
  · intro v hv
    rw [mem_fixedByEnd]
    exact blockEnd_apply_of_ker A hp hpF hA t ht D (by rw [LinearMap.mem_ker]; exact hv)

theorem mem_blockSpace_of_commute {B : LinearMap.BilinForm F V} (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A) (halt : B.IsAlt)
    (hB : InvariantBilin A B) (hBn : B.Nondegenerate)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) {D : Hyperplane A p}
    {g : V ≃ₗ[F] V} (hg : Commute g (blockEnd A hp hpF hA t ht D))
    (hgiso : ∀ u v, B (g u) (g v) = B u v) {v : V} (hv : v ∈ blockSpace A D.1) :
    g v ∈ blockSpace A D.1 := by
  have hker : fixedByEnd (blockEnd A hp hpF hA t ht D) =
      LinearMap.ker (projBlock A hp hpF hA D) := fixedByEnd_blockEnd_eq_ker A hp hpF hA t ht D
  have horth : B.orthogonal (LinearMap.ker (projBlock A hp hpF hA D)) =
      blockSpace A D.1 := by
    rw [← orthogonal_blockSpace_eq_ker A hp hpF hA hB hBn D]
    exact LinearMap.BilinForm.orthogonal_orthogonal hBn halt.isRefl (blockSpace A D.1)
  rw [← horth]
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro u hu
  have hgu : g⁻¹ u ∈ LinearMap.ker (projBlock A hp hpF hA D) := by
    rw [← hker, mem_fixedByEnd]
    have hu' : (blockEnd A hp hpF hA t ht D) u = u := by
      rw [← hker, mem_fixedByEnd] at hu; exact hu
    calc (blockEnd A hp hpF hA t ht D) (g⁻¹ u)
        = g⁻¹ ((blockEnd A hp hpF hA t ht D) u) := by
          have := hg.inv_left.eq
          exact congrArg (fun e => e u) this.symm
      _ = g⁻¹ u := by rw [hu']
  have hiso : B u (g v) = B (g⁻¹ u) v := by
    have h := hgiso (g⁻¹ u) v
    rw [show g (g⁻¹ u) = u from g.apply_symm_apply u] at h
    exact h
  have hv' : v ∈ B.orthogonal (LinearMap.ker (projBlock A hp hpF hA D)) := by
    rw [horth]; exact hv
  rw [hiso]
  exact LinearMap.BilinForm.mem_orthogonal_iff.mp hv' (g⁻¹ u) hgu

theorem six_le_finrank_orthogonal_blockSpace {B : LinearMap.BilinForm F V} (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A) (hB : InvariantBilin A B)
    (hBn : B.Nondegenerate) (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    {D E G : Hyperplane A p} (hDE : D ≠ E) (hDG : D ≠ G) (hEG : E ≠ G)
    (hDE' : Module.finrank F ↥(blockSpace A D.1) ≤
      Module.finrank F ↥(blockSpace A E.1))
    (hDG' : Module.finrank F ↥(blockSpace A D.1) ≤
      Module.finrank F ↥(blockSpace A G.1))
    (hV : 9 ≤ Module.finrank F V) :
    6 ≤ Module.finrank F ↥(B.orthogonal (blockSpace A D.1)) := by
  have hdimC := finrank_fixedByEnd_blockEnd A hp hpF hA t ht D
  have hthree := three_mul_finrank_blockSpace_le A hp hpF hA hDE hDG hEG hDE' hDG'
  have htwo := two_mul_finrank_le_three_mul_finrank_fixedByEnd A hp hpF hA t ht hDE hDG hEG
    hDE' hDG'
  have hker := fixedByEnd_blockEnd_eq_ker A hp hpF hA t ht D
  rw [orthogonal_blockSpace_eq_ker A hp hpF hA hB hBn D, ← hker]
  omega

theorem finrank_blockSpace_sup_le [FiniteDimensional F V] (hp : p.Prime)
    (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A) {D E G : Hyperplane A p}
    (hDE : D ≠ E) (hDG : D ≠ G) (hEG : E ≠ G) :
    Module.finrank F ↥(blockSpace A D.1) + Module.finrank F ↥(blockSpace A E.1) +
        Module.finrank F ↥(blockSpace A G.1) ≤ Module.finrank F V := by
  classical
  have hdisj : ∀ i : Hyperplane A p, Disjoint (blockSpace A i.1)
      (⨆ j, ⨆ (_ : j ≠ i), blockSpace A j.1) :=
    iSupIndep_def.mp (iSupIndep_blockSpace A hp hpF hA)
  have hEGbot : blockSpace A E.1 ⊓ blockSpace A G.1 = ⊥ := by
    have h := disjoint_iff_inf_le.mp (hdisj E)
    refine le_bot_iff.mp (le_trans ?_ h)
    exact inf_le_inf_left _ (le_iSup₂ (f := fun j (_ : j ≠ E) => blockSpace A j.1) G
      (Ne.symm hEG))
  have hDbot : blockSpace A D.1 ⊓ (blockSpace A E.1 ⊔ blockSpace A G.1) = ⊥ := by
    have h := disjoint_iff_inf_le.mp (hdisj D)
    refine le_bot_iff.mp (le_trans ?_ h)
    refine inf_le_inf_left _ (sup_le ?_ ?_)
    · exact le_iSup₂ (f := fun j (_ : j ≠ D) => blockSpace A j.1) E (Ne.symm hDE)
    · exact le_iSup₂ (f := fun j (_ : j ≠ D) => blockSpace A j.1) G (Ne.symm hDG)
  have hEG : Module.finrank F ↥(blockSpace A E.1 ⊔ blockSpace A G.1) =
      Module.finrank F ↥(blockSpace A E.1) + Module.finrank F ↥(blockSpace A G.1) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (blockSpace A E.1) (blockSpace A G.1)
    rw [hEGbot, finrank_bot, add_zero] at h
    omega
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (blockSpace A D.1)
    (blockSpace A E.1 ⊔ blockSpace A G.1)
  rw [hDbot, finrank_bot, add_zero, hEG] at hsup
  have hle : Module.finrank F ↥(blockSpace A D.1 ⊔
      (blockSpace A E.1 ⊔ blockSpace A G.1)) ≤ Module.finrank F V := by
    have h := Submodule.finrank_mono (le_top : blockSpace A D.1 ⊔
      (blockSpace A E.1 ⊔ blockSpace A G.1) ≤ (⊤ : Submodule F V))
    rwa [finrank_top] at h
  omega

theorem four_le_finrank_orthogonal_sup_blockSpace {B : LinearMap.BilinForm F V}
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A) (hB : InvariantBilin A B)
    (hBn : B.Nondegenerate) {D E G : Hyperplane A p}
    (hDE : D ≠ E) (hDG : D ≠ G) (hEG : E ≠ G)
    (hDE' : Module.finrank F ↥(blockSpace A D.1) ≤
      Module.finrank F ↥(blockSpace A E.1))
    (hEG' : Module.finrank F ↥(blockSpace A E.1) ≤
      Module.finrank F ↥(blockSpace A G.1))
    (hV : 10 ≤ Module.finrank F V) :
    4 ≤ Module.finrank F ↥(B.orthogonal (blockSpace A D.1 ⊔ blockSpace A E.1)) := by
  classical
  have hsum := finrank_blockSpace_sup_le A hp hpF hA hDE hDG hEG
  have hdisj : Disjoint (blockSpace A D.1) (blockSpace A E.1) := by
    refine disjoint_iff_inf_le.mpr ?_
    have h := disjoint_iff_inf_le.mp
      ((iSupIndep_def.mp (iSupIndep_blockSpace A hp hpF hA)) D)
    exact (inf_le_inf_left _ (le_iSup₂ (f := fun j (_ : j ≠ D) => blockSpace A j.1) E
      (Ne.symm hDE))).trans h
  have hsup : Module.finrank F ↥(blockSpace A D.1 ⊔ blockSpace A E.1) =
      Module.finrank F ↥(blockSpace A D.1) + Module.finrank F ↥(blockSpace A E.1) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (blockSpace A D.1) (blockSpace A E.1)
    rw [hdisj.eq_bot, finrank_bot, add_zero] at h
    omega
  have horth := LinearMap.BilinForm.finrank_orthogonal hBn (blockSpace A D.1 ⊔ blockSpace A E.1)
  rw [horth, hsup]
  omega

end SpEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F
