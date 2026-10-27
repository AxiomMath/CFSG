module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveYpsModel

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {F : Type*} [Field F]

@[expose] def antiTFive (M : Matrix (Fin 5) (Fin 5) F) : Matrix (Fin 5) (Fin 5) F :=
  Matrix.of fun i j => M (Fin.rev j) (Fin.rev i)

omit [Field F] in
theorem antiTFive_apply (M : Matrix (Fin 5) (Fin 5) F) (i j : Fin 5) :
    antiTFive M i j = M (Fin.rev j) (Fin.rev i) := rfl

theorem antiTFive_mul (M N : Matrix (Fin 5) (Fin 5) F) :
    antiTFive (M * N) = antiTFive N * antiTFive M := by
  ext i j
  simp only [antiTFive_apply, Matrix.mul_apply]
  rw [← Equiv.sum_comp Fin.revPerm]
  simp [mul_comm]

theorem antiTFive_one : antiTFive (1 : Matrix (Fin 5) (Fin 5) F) = 1 := by
  ext i j
  simp only [antiTFive_apply, Matrix.one_apply, Fin.rev_inj]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

omit [Field F] in
theorem antiTFive_antiTFive (M : Matrix (Fin 5) (Fin 5) F) : antiTFive (antiTFive M) = M := by
  ext i j
  simp [antiTFive_apply]

theorem det_antiTFive (M : Matrix (Fin 5) (Fin 5) F) : (antiTFive M).det = M.det := by
  have h : antiTFive M = (M.submatrix Fin.revPerm Fin.revPerm)ᵀ := by
    ext i j
    rfl
  rw [h, det_transpose, det_submatrix_equiv_self]

@[expose] def graphSLFive : SpecialLinearGroup (Fin 5) F →* SpecialLinearGroup (Fin 5) F where
  toFun x := ⟨antiTFive ((x⁻¹ : SpecialLinearGroup (Fin 5) F) : Matrix (Fin 5) (Fin 5) F), by
    rw [det_antiTFive]
    exact (x⁻¹).2⟩
  map_one' := Subtype.ext (by
    change antiTFive ((1⁻¹ : SpecialLinearGroup (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = 1
    rw [inv_one]
    exact antiTFive_one)
  map_mul' x y := Subtype.ext (by
    change antiTFive (((x * y)⁻¹ : SpecialLinearGroup (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) =
      antiTFive ((x⁻¹ : SpecialLinearGroup (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) *
        antiTFive ((y⁻¹ : SpecialLinearGroup (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)
    rw [_root_.mul_inv_rev, SpecialLinearGroup.coe_mul, antiTFive_mul])

theorem coe_graphSLFive (x : SpecialLinearGroup (Fin 5) F) :
    ((graphSLFive x : SpecialLinearGroup (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) =
      antiTFive ((x⁻¹ : SpecialLinearGroup (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) := rfl

theorem graphSLFive_graphSLFive (x : SpecialLinearGroup (Fin 5) F) :
    graphSLFive (graphSLFive x) = x := by
  apply Subtype.ext
  change antiTFive (((graphSLFive x)⁻¹ : SpecialLinearGroup (Fin 5) F) :
    Matrix (Fin 5) (Fin 5) F) = _
  rw [← map_inv, coe_graphSLFive, inv_inv, antiTFive_antiTFive]

theorem graphSLFive_mem_unitriangular {x : SpecialLinearGroup (Fin 5) F}
    (hx : x ∈ unitriangular 5 F) : graphSLFive x ∈ unitriangular 5 F := by
  have hx' := (unitriangular 5 F).inv_mem hx
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [coe_graphSLFive, antiTFive_apply]
    exact hx'.1 _ _ (Fin.rev_lt_rev.2 hij)
  · rw [coe_graphSLFive, antiTFive_apply]
    exact hx'.2 _

@[expose] def uFiveGraph : MulAut (unitriangular 5 F) where
  toFun x := ⟨graphSLFive (x : SpecialLinearGroup (Fin 5) F), graphSLFive_mem_unitriangular x.2⟩
  invFun x := ⟨graphSLFive (x : SpecialLinearGroup (Fin 5) F), graphSLFive_mem_unitriangular x.2⟩
  left_inv _ := Subtype.ext (graphSLFive_graphSLFive _)
  right_inv _ := Subtype.ext (graphSLFive_graphSLFive _)
  map_mul' x y := Subtype.ext (map_mul graphSLFive (x : SpecialLinearGroup (Fin 5) F) y)

theorem ypsMat_uFiveGraph_apply (x : unitriangular 5 F) (i j : Fin 5) :
    ypsMat (uFiveGraph x) i j = ypsMat x⁻¹ (Fin.rev j) (Fin.rev i) := rfl

theorem uFiveGraph_uFiveGraph (x : unitriangular 5 F) : uFiveGraph (uFiveGraph x) = x :=
  Subtype.ext (graphSLFive_graphSLFive _)

theorem ypsMat_inv_apply_succ (x : unitriangular 5 F) (k : Fin 4) :
    ypsMat x⁻¹ k.castSucc k.succ = -ypsMat x k.castSucc k.succ := by
  have h := ypsMat_mul_apply_succ x x⁻¹ k
  rw [mul_inv_cancel, ypsMat_one, Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := k)).ne] at h
  linear_combination -h

theorem fin_rev_five : Fin.rev (0 : Fin 5) = 4 ∧ Fin.rev (1 : Fin 5) = 3 ∧ Fin.rev (2 : Fin 5) = 2 ∧
    Fin.rev (3 : Fin 5) = 1 ∧ Fin.rev (4 : Fin 5) = 0 := by decide

theorem ypsMat_uFiveGraph_apply34 (x : unitriangular 5 F) :
    ypsMat (uFiveGraph x) 3 4 = -ypsMat x 0 1 := by
  obtain ⟨-, -, -, r3, r4⟩ := fin_rev_five
  rw [ypsMat_uFiveGraph_apply, r4, r3]
  exact ypsMat_inv_apply_succ x 0

section Finite

variable [Finite F]

theorem uFiveGraph_mem_uFiveCol {x : unitriangular 5 F} (hx : x ∈ uFiveRow) :
    uFiveGraph x ∈ uFiveCol := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := uFiveRow.inv_mem hx
  obtain ⟨r0, r1, r2, r3, -⟩ := fin_rev_five
  rw [mem_uFiveCol]
  simp only [ypsMat_uFiveGraph_apply, r0, r1, r2, r3]
  exact ⟨h6, h5, h3, h4, h2, h1⟩

theorem uFiveGraph_mem_uFiveRow {x : unitriangular 5 F} (hx : x ∈ uFiveCol) :
    uFiveGraph x ∈ uFiveRow := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := uFiveCol.inv_mem hx
  obtain ⟨-, r1, r2, r3, r4⟩ := fin_rev_five
  rw [mem_uFiveRow]
  simp only [ypsMat_uFiveGraph_apply, r1, r2, r3, r4]
  exact ⟨h6, h5, h3, h4, h2, h1⟩

theorem map_uFiveGraph_uFiveRow :
    (uFiveRow (F := F)).map uFiveGraph.toMonoidHom = uFiveCol := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact uFiveGraph_mem_uFiveCol hx
  · intro hy
    exact ⟨uFiveGraph y, uFiveGraph_mem_uFiveRow hy, uFiveGraph_uFiveGraph y⟩

end Finite

end CFSG.SeitzReduction.LinearPilot
