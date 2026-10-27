module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix CFSG.Glauberman.Dickson

variable {E : Type} [Field E]

theorem trace_sq_mem_of_witness {p m : ℕ} (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) E))
    (W : SubfieldConjugacyWitness p m H) (g : SpecialLinearGroup (Fin 2) E)
    (hg : (QuotientGroup.mk g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) ∈ H) :
    (g : Matrix (Fin 2) (Fin 2) E).trace ^ 2 ∈ W.K := by
  let h : H := ⟨QuotientGroup.mk g, hg⟩
  obtain ⟨B, hB⟩ := Matrix.ProjGenLinGroup.mk_surjective (W.phi h)
  obtain ⟨C, hC⟩ := Matrix.ProjGenLinGroup.mk_surjective W.conjugator
  have hmap := W.map_phi h
  rw [← hB, h826_pglMap_mk, ← hC] at hmap
  have h2 : h826_pslToPGL (h : Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) =
      Matrix.ProjGenLinGroup.mk (SpecialLinearGroup.toGL g) := h826_pslToPGL_mk g
  rw [h2, ← map_inv, ← map_mul, ← map_mul] at hmap
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.1 hmap
  set Mx : Matrix (Fin 2) (Fin 2) E :=
    ((Matrix.GeneralLinearGroup.map W.K.subtype B : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E)
    with hMx
  have hentry : ∀ i j, Mx i j ∈ W.K := fun i j => (B i j).2
  have hG' : ((C * SpecialLinearGroup.toGL g * C⁻¹ : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) =
      (u : E) • Mx := by
    rw [← hu, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_mul_diagonal]
  have hgv : ((SpecialLinearGroup.toGL g : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) =
      (g : Matrix (Fin 2) (Fin 2) E) := rfl
  have htr : (g : Matrix (Fin 2) (Fin 2) E).trace = u * Mx.trace := by
    have h1 := congrArg Matrix.trace hG'
    rw [Matrix.trace_smul, smul_eq_mul] at h1
    rw [← h1, Units.val_mul, Units.val_mul, hgv, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have hdet : 1 = (u : E) ^ 2 * Mx.det := by
    have h1 := congrArg Matrix.det hG'
    rw [Matrix.det_smul, Fintype.card_fin] at h1
    rw [← h1, Units.val_mul, Units.val_mul, hgv]
    have := Matrix.det_units_conj C (g : Matrix (Fin 2) (Fin 2) E)
    rw [this]; exact g.2.symm
  have hdet0 : Mx.det ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hdet; exact one_ne_zero hdet
  have hT : Mx.trace ∈ W.K := by
    rw [Matrix.trace_fin_two]; exact W.K.add_mem (hentry 0 0) (hentry 1 1)
  have hD : Mx.det ∈ W.K := by
    rw [Matrix.det_fin_two]
    exact W.K.sub_mem (W.K.mul_mem (hentry 0 0) (hentry 1 1)) (W.K.mul_mem (hentry 0 1) (hentry 1 0))
  have hu2 : (u : E) ^ 2 = (Mx.det)⁻¹ := by
    exact eq_inv_of_mul_eq_one_left hdet.symm
  rw [htr, mul_pow, hu2]
  exact W.K.mul_mem (W.K.inv_mem hD) (W.K.pow_mem hT 2)

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
