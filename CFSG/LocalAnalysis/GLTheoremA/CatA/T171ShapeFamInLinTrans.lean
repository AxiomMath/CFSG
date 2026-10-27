module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInLinTransJ
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBlockDefs
import CFSG.Assembly.GL83StatedBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement MatrixGroups

theorem projConj_apply_mk {K : Type} [Field K] {N : ℕ} (D : GL (Fin N) K)
    (hD : D ∈ Subgroup.normalizer (StatedSL N K : Set (GL (Fin N) K)))
    {h h' : ↥(StatedSL N K)} (hh : (h' : GL (Fin N) K) = D * (h : GL (Fin N) K) * D⁻¹) :
    TableB.projConj (StatedSL N K) ⟨D, hD⟩ (LargeEvenProjMk (StatedSL N K) h) =
      LargeEvenProjMk (StatedSL N K) h' := by
  rw [show LargeEvenProjMk (StatedSL N K) h = (h : LargeEvenProj (StatedSL N K)) from rfl,
    show LargeEvenProjMk (StatedSL N K) h' = (h' : LargeEvenProj (StatedSL N K)) from rfl,
    TableB.projConj_mk]
  congr 1
  apply Subtype.ext
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hh]

@[expose] def LinBlockInnDiagStated : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G) (N n : ℕ)
    (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ n → WSetup p L J A d b →
    ∀ (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (StatedSL N K))
      (D B : GL (Fin N) K)
      (hD : D ∈ Subgroup.normalizer (StatedSL N K : Set (GL (Fin N) K)))
      (hB : B ∈ Subgroup.normalizer (StatedSL N K : Set (GL (Fin N) K))),
      D ^ p = 1 → Commute D B →
      LargeEvenInduces θ (conjRel d) (TableB.projConj (StatedSL N K) ⟨D, hD⟩) →
      LargeEvenInduces θ (conjRel b) (TableB.projConj (StatedSL N K) ⟨B, hB⟩) →
      InnDiagOn p (Subgroup.zpowers b) J

theorem linBlockInnDiag_of_stated (h : LinBlockInnDiagStated) : LinBlockInnDiag := by
  intro G _ _ p L J A d b N n K _ _ hK hS
  have key : ∀ H : Subgroup (GL (Fin N) K), H = StatedSL N K →
      ∀ (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj H) (D B : GL (Fin N) K)
        (hD : D ∈ Subgroup.normalizer (H : Set (GL (Fin N) K)))
        (hB : B ∈ Subgroup.normalizer (H : Set (GL (Fin N) K))),
        D ^ p = 1 → Commute D B →
        LargeEvenInduces θ (conjRel d) (TableB.projConj H ⟨D, hD⟩) →
        LargeEvenInduces θ (conjRel b) (TableB.projConj H ⟨B, hB⟩) →
        InnDiagOn p (Subgroup.zpowers b) J := by
    rintro H rfl
    exact h G p L J A d b N n K hK hS
  exact key _ (CFSG.Assembly.largeEvenSLGroup_eq_statedSL N)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
