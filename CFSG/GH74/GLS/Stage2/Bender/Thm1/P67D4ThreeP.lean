module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.AlgebraicGroups.RationalCentralizerCocycleComponents
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix
public import CFSG.RankThree.PartOne.KE.CTRational
public import CFSG.RankThree.PartOne.KGD.D4Weyl

public section

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KGD
open scoped Matrix Pointwise

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem perm_eq_one_of_weyl_eq_permLattice
    (w : WeylGroup TwistTag.D4.tag)
    (π : Equiv.Perm (Fin TwistTag.D4.tag.rank))
    (h : ∀ x : Fin TwistTag.D4.tag.rank → ℤ, w • x = permLattice π x) : π = 1 := by
  have hw1 : w = 1 := eq_one_of_forall_height_pos fun i => by
    rw [h, permLattice_single, height_single]
    exact one_pos
  subst hw1
  ext i
  have h1 := h (Pi.single i 1)
  rw [one_smul, permLattice_single] at h1
  have h2 := congrFun h1 i
  simp only [Pi.single_apply, ↓reduceIte] at h2
  by_contra hne
  have h3 : ¬ (i = π i) := fun h4 => hne (by simp [← h4])
  simp [h3] at h2

section Diag

variable {L : Type} [Field L]

theorem conj_diagramMap_pow_mem_adjointGroup
    (k : ℕ)
    {g : ModGL TwistTag.D4.tag L} (hg : g ∈ adjointGroup TwistTag.D4.tag L) :
    diagramMap TwistTag.D4 L ^ k * g * (diagramMap TwistTag.D4 L ^ k)⁻¹ ∈
      adjointGroup TwistTag.D4.tag L := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    have h1 := twistHom_mem_adjointGroup TwistTag.D4 L (RingHom.id L) ih
    rw [twistHom_apply] at h1
    have h2 : Units.map (entrywiseHom (RingHom.id L))
        (diagramMap TwistTag.D4 L ^ k * g * (diagramMap TwistTag.D4 L ^ k)⁻¹) =
        diagramMap TwistTag.D4 L ^ k * g * (diagramMap TwistTag.D4 L ^ k)⁻¹ :=
      Units.ext (entrywise_id _)
    rw [h2] at h1
    have h3 : diagramMap TwistTag.D4 L ^ (k + 1) * g * (diagramMap TwistTag.D4 L ^ (k + 1))⁻¹ =
        diagramMap TwistTag.D4 L * (diagramMap TwistTag.D4 L ^ k * g *
          (diagramMap TwistTag.D4 L ^ k)⁻¹) * (diagramMap TwistTag.D4 L)⁻¹ := by
      rw [pow_succ', _root_.mul_inv_rev]
      group
    rw [h3]
    exact h1

theorem diagramMap_pow_conj_rootDiagUnit
    (a : Fin TwistTag.D4.tag.rank → Lˣ) (k : ℕ) :
    diagramMap TwistTag.D4 L ^ k * rootDiagUnit TwistTag.D4.tag a *
        (diagramMap TwistTag.D4 L ^ k)⁻¹ =
      rootDiagUnit TwistTag.D4.tag (fun i => a (((TwistTag.D4.perm.symm) ^ k) i)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h3 : diagramMap TwistTag.D4 L ^ (k + 1) * rootDiagUnit TwistTag.D4.tag a *
        (diagramMap TwistTag.D4 L ^ (k + 1))⁻¹ =
        diagramMap TwistTag.D4 L * (diagramMap TwistTag.D4 L ^ k *
          rootDiagUnit TwistTag.D4.tag a * (diagramMap TwistTag.D4 L ^ k)⁻¹) *
          (diagramMap TwistTag.D4 L)⁻¹ := by
      rw [pow_succ', _root_.mul_inv_rev]
      group
    rw [h3, ih]
    have h4 := twistHom_rootDiagUnit_eq (t := TwistTag.D4) (σ := RingHom.id L)
      (fun i => a (((TwistTag.D4.perm.symm) ^ k) i))
    rw [twistHom_apply] at h4
    have h5 : Units.map (entrywiseHom (RingHom.id L))
        (rootDiagUnit TwistTag.D4.tag (fun i => a (((TwistTag.D4.perm.symm) ^ k) i))) =
        rootDiagUnit TwistTag.D4.tag (fun i => a (((TwistTag.D4.perm.symm) ^ k) i)) :=
      Units.ext (entrywise_id _)
    rw [h5] at h4
    rw [h4]
    congr 1

end Diag

end CFSG.GH74.GLS.Stage2.Bender.Thm1
