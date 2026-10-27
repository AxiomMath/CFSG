module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpDef

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421SpProof

open Matrix K421MonoProof K421OrbProof K421LinProof K421CGProof

section Bd

variable {F : Type} [Field F] [CharP F 2]

@[expose] def bd (d : Fin 3 → Matrix (Fin 2) (Fin 2) F) : Matrix Idx Idx F :=
  Matrix.of fun i j => if i.1 = j.1 then d i.1 i.2 j.2 else 0

theorem bd_eq_comp (d : Fin 3 → Matrix (Fin 2) (Fin 2) F) :
    bd d = Matrix.compRingEquiv (Fin 3) (Fin 2) F (Matrix.diagonal d) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [bd, Matrix.of_apply, Matrix.compRingEquiv_apply, Matrix.comp_apply,
    Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    rfl
  · rfl

theorem bd_mul (d d' : Fin 3 → Matrix (Fin 2) (Fin 2) F) :
    bd d * bd d' = bd (fun j => d j * d' j) := by
  rw [bd_eq_comp, bd_eq_comp, bd_eq_comp, ← map_mul, Matrix.diagonal_mul_diagonal]

theorem bd_one : bd (fun _ => (1 : Matrix (Fin 2) (Fin 2) F)) = 1 := by
  rw [bd_eq_comp, Matrix.diagonal_one, map_one]

theorem bd_transpose (d : Fin 3 → Matrix (Fin 2) (Fin 2) F) :
    (bd d)ᵀ = bd (fun j => (d j)ᵀ) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [bd, Matrix.transpose_apply, Matrix.of_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem bd_injective {d d' : Fin 3 → Matrix (Fin 2) (Fin 2) F} (h : bd d = bd d') : d = d' := by
  funext j
  ext a b
  have := congrFun (congrFun h (j, a)) (j, b)
  simpa [bd] using this

@[expose] def bdGL : (Fin 3 → GL (Fin 2) F) →* GL Idx F where
  toFun y := ⟨bd (fun j => ((y j : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)),
    bd (fun j => (((y j)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)),
    by rw [bd_mul]; simp [bd_one],
    by rw [bd_mul]; simp [bd_one]⟩
  map_one' := Units.ext (by
    show bd (fun j => (((1 : Fin 3 → GL (Fin 2) F) j : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)) = 1
    simp [bd_one])
  map_mul' y y' := Units.ext (by
    show bd (fun j => (((y * y') j : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) =
      bd (fun j => ((y j : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
        bd (fun j => ((y' j : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
    rw [bd_mul]
    rfl)

theorem bdGL_injective : Function.Injective (bdGL (F := F)) := by
  intro y y' h
  have h0 : bd (fun j => ((y j : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) =
      bd (fun j => ((y' j : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) := congrArg Units.val h
  have h1 := bd_injective h0
  funext j
  exact Units.ext (congrFun h1 j)

theorem JF_eq_bd : JF F = bd (fun _ => (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F)) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [JF, bc, JI, bd, Matrix.map_apply, Matrix.of_apply]
  split_ifs with h
  · fin_cases a <;> fin_cases b <;> simp [Jm]
  · simp

end Bd

end K421SpProof

end CFSG.LocalAnalysis.RankThreeUC.S15
