module

public import CFSG.CharacterTheory.PSL2Table.Basic
public import Mathlib.LinearAlgebra.Projectivization.Action

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open Matrix
open scoped LinearAlgebra.Projectivization MatrixGroups

def borelPoint (F : Type) [Field F] : ℙ F (Fin 2 → F) :=
  Projectivization.mk F ![(1 : F), 0] (by simp)

theorem nontrivial_borelPoint (F : Type) [Field F] : Nontrivial (ℙ F (Fin 2 → F)) := by
  refine ⟨borelPoint F, Projectivization.mk F ![(0 : F), 1] (by simp), ?_⟩
  intro h
  have h' : Projectivization.mk F ![(1 : F), 0] (by simp) =
      Projectivization.mk F ![(0 : F), 1] (by simp) := h
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff' F ![(1 : F), 0] ![(0 : F), 1] (by simp) (by simp)).mp h'
  have h0 := congrFun ha 0
  simp at h0

theorem stabilizer_borelSL (F : Type) [Field F] :
    MulAction.stabilizer (SL(2, F)) (borelPoint F) = CFSG.PSL2Table.borelSL F := by
  ext A
  rw [MulAction.mem_stabilizer_iff, CFSG.PSL2Table.mem_borelSL_iff]
  constructor
  · intro h
    have h' : A • borelPoint F = borelPoint F := h
    rw [borelPoint, Projectivization.smul_mk] at h'
    obtain ⟨a, ha⟩ :=
      (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp h'
    have h1 := congrFun ha 1
    simpa [Matrix.SpecialLinearGroup.smul_def, Matrix.mulVec, dotProduct] using h1.symm
  · intro h10
    rw [borelPoint, Projectivization.smul_mk]
    refine (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr
      ⟨(A : Matrix (Fin 2) (Fin 2) F) 0 0, ?_⟩
    ext i
    fin_cases i <;>
      simp [h10, Matrix.SpecialLinearGroup.smul_def, Matrix.mulVec, dotProduct]

theorem stabilizer_borel (F : Type) [Field F] :
    MulAction.stabilizer (PSL(2, F)) (borelPoint F) = CFSG.PSL2Table.borel F := by
  ext g
  constructor
  · intro hg
    obtain ⟨A, rfl⟩ := CFSG.PSL2Table.mk_surjective g
    have hg' : A • borelPoint F = borelPoint F := by
      rw [MulAction.mem_stabilizer_iff] at hg
      simpa only [CFSG.PSL2Table.mk, QuotientGroup.mk'_apply,
        Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk] using hg
    rw [CFSG.PSL2Table.mk_mem_borel_iff, ← stabilizer_borelSL,
      MulAction.mem_stabilizer_iff]
    exact hg'
  · intro hg
    obtain ⟨A, rfl⟩ := CFSG.PSL2Table.mk_surjective g
    rw [MulAction.mem_stabilizer_iff]
    have hA : A • borelPoint F = borelPoint F := by
      rw [← MulAction.mem_stabilizer_iff, stabilizer_borelSL]
      exact (CFSG.PSL2Table.mk_mem_borel_iff A).mp hg
    simpa only [CFSG.PSL2Table.mk, QuotientGroup.mk'_apply,
      Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk] using hA

theorem borel_overgroup_eq_borel_or_top {F : Type} [Field F] [Finite F]
    {Y : Subgroup (PSL(2, F))} (h : CFSG.PSL2Table.borel F ≤ Y) :
    Y = CFSG.PSL2Table.borel F ∨ Y = ⊤ := by
  haveI : Nontrivial (ℙ F (Fin 2 → F)) := nontrivial_borelPoint F
  have hcoat : IsCoatom (CFSG.PSL2Table.borel F) := by
    rw [← stabilizer_borel]
    exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive
      (G := PSL(2, F)) (borelPoint F)
  exact Or.comm.mp (hcoat.le_iff.mp h)

theorem borelSL_overgroup_eq_borelSL_or_top {F : Type} [Field F] [Finite F]
    {Y : Subgroup (SL(2, F))} (h : CFSG.PSL2Table.borelSL F ≤ Y) :
    Y = CFSG.PSL2Table.borelSL F ∨ Y = ⊤ := by
  haveI : Nontrivial (ℙ F (Fin 2 → F)) := nontrivial_borelPoint F
  have hcoat : IsCoatom (CFSG.PSL2Table.borelSL F) := by
    rw [← stabilizer_borelSL]
    exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive
      (G := SL(2, F)) (borelPoint F)
  exact Or.comm.mp (hcoat.le_iff.mp h)

end CFSG.LocalAnalysis.AGL81I.Section3
