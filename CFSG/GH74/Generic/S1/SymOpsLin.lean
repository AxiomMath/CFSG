module

public import CFSG.GH74.Generic.S1.SymCore
public import CFSG.GH74.Generic.S1.SymDiagLin

public section

namespace CFSG.GH74.Generic.S1

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup

variable {F : Type} [Field F]

theorem commutant_lin (M : GL (Fin 4) F) (hM : ∀ k ∈ StatedSL 4 F, M * k = k * M) :
    ∃ c : F, (M : Matrix (Fin 4) (Fin 4) F) = c • (1 : Matrix (Fin 4) (Fin 4) F) := by
  have h : (M : Matrix (Fin 4) (Fin 4) F) ∈ Set.range (Matrix.scalar (Fin 4)) := by
    apply Matrix.mem_range_scalar_of_commute_transvectionStruct
    intro t
    have hdet : (t.toMatrix : Matrix (Fin 4) (Fin 4) F).det = 1 := t.det
    let T : GL (Fin 4) F := Matrix.GeneralLinearGroup.mk'' t.toMatrix (by rw [hdet]; exact isUnit_one)
    have hT : T ∈ StatedSL 4 F := by
      rw [statedSL_eq_detOne, mem_detOne]
      exact hdet
    have h1 := congrArg Units.val (hM T hT)
    exact h1.symm
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  rw [← hc]
  simp [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

def linOps [Finite F] (h2 : (2 : F) ≠ 0) : ModelOps F (StatedSL 4 F) where
  norm := fun _ => True
  norm_conj := fun P _ => ⟨fun k hk => conj_mem_statedSL P hk,
    fun k hk => by simpa using conj_mem_statedSL P⁻¹ hk⟩
  std := fun _ => True
  to_std := fun ρ _ _ _ => ⟨ρ, Or.inl rfl, trivial⟩
  commutant := commutant_lin
  diag := fun ρ hρ2 hdet _ hcomm hne => by
    obtain ⟨P, ε, hε, h⟩ := exists_diag_frame_lin h2 ρ hρ2 hdet hcomm hne
    exact ⟨P, ε, trivial, hε, h⟩

end CFSG.GH74.Generic.S1
