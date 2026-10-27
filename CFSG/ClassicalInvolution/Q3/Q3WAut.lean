module

public import CFSG.ClassicalInvolution.Q3.Q3WCoord

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

variable {K : Type} [Field K]

variable [Finite K]

theorem exists_extend_unip (α : SL(2, K) ≃* SL(2, K))
    (h₁ : ∃ t : K, α (xp 1) = xp t ∨ α (xp 1) = xm t)
    (h₂ : ∃ t : K, α (xm 1) = xp t ∨ α (xm 1) = xm t) :
    ∃ β : SL(3, K) ≃* SL(3, K),
      (∀ A, β (blockSL K 3 2 0 (by omega) A) = blockSL K 3 2 0 (by omega) (α A)) ∧
        (B23 K).map β.toMonoidHom = B23 K ∧
        ∃ γ : SL(2, K) ≃* SL(2, K),
          (∀ C, β (blockSL K 3 2 1 (by omega) C) = blockSL K 3 2 1 (by omega) (γ C)) ∧
            ∀ g ∈ coordSet K, γ g ∈ coordSet K := by
  obtain ⟨G, ψ, hG⟩ := CFSG.ClassicalInvolution.Phan.exists_toGL_eq_conj_map α
  have hcoe : ∀ A : SL(2, K), ((α A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      (G : Matrix (Fin 2) (Fin 2) K) *
        ((Matrix.SpecialLinearGroup.map (ψ : K →+* K) A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
          ((G⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    intro A
    have h2 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) (hG A)
    simpa only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using h2
  have hkey : ∀ A : SL(2, K), ((α A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
      (G : Matrix (Fin 2) (Fin 2) K) = (G : Matrix (Fin 2) (Fin 2) K) *
        ((Matrix.SpecialLinearGroup.map (ψ : K →+* K) A : SL(2, K)) :
          Matrix (Fin 2) (Fin 2) K) := by
    intro A
    rw [hcoe A]
    simp only [Matrix.mul_assoc, G.inv_mul, Matrix.mul_one]
  have e1 := hkey (xp 1)
  have e2 := hkey (xm 1)
  rw [map_xp, map_one] at e1
  rw [map_xm, map_one] at e2
  have hdet : (G : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := (Matrix.isUnits_det_units G).ne_zero
  have f1 : (G : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∨ (G : Matrix (Fin 2) (Fin 2) K) 0 0 = 0 := by
    obtain ⟨t, ht | ht⟩ := h₁
    · left
      rw [ht] at e1
      have := congrFun (congrFun e1 1) 1
      simp [xp, Matrix.mul_apply, Fin.sum_univ_two] at this
      exact this
    · right
      rw [ht] at e1
      have := congrFun (congrFun e1 0) 1
      simp [xp, xm, Matrix.mul_apply, Fin.sum_univ_two] at this
      exact this
  have f2 : (G : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 ∨ (G : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    obtain ⟨t, ht | ht⟩ := h₂
    · left
      rw [ht] at e2
      have := congrFun (congrFun e2 1) 0
      simp [xp, xm, Matrix.mul_apply, Fin.sum_univ_two] at this
      exact this
    · right
      rw [ht] at e2
      have := congrFun (congrFun e2 0) 0
      simp [xm, Matrix.mul_apply, Fin.sum_univ_two] at this
      exact this
  have hmono : ((G : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧ (G : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) ∨
      ((G : Matrix (Fin 2) (Fin 2) K) 0 0 = 0 ∧ (G : Matrix (Fin 2) (Fin 2) K) 1 1 = 0) := by
    rw [Matrix.det_fin_two] at hdet
    rcases f1 with h10 | h00 <;> rcases f2 with h11 | h01
    · exact absurd (by rw [h10, h11]; ring) hdet
    · exact Or.inl ⟨h01, h10⟩
    · exact Or.inr ⟨h00, h11⟩
    · exact absurd (by rw [h00, h01]; ring) hdet
  rcases hmono with ⟨h01, h10⟩ | ⟨h00, h11⟩
  · obtain ⟨a, b, hGa, hGi⟩ := exists_diagonal_of_offDiag_zero G h01 h10
    have hα' : ∀ A, α A = diagConj2 a b (fieldAutSL ψ 2 A) := fun A =>
      Subtype.ext (by rw [hcoe A, hGa, hGi]; rfl)
    have hβ0 : ∀ A, (fieldAutSL ψ 3).trans (diagConj3 a b) (blockSL K 3 2 0 (by omega) A) =
        blockSL K 3 2 0 (by omega) (α A) := fun A => by
      show diagConj3 a b (fieldAutSL ψ 3 (blockSL K 3 2 0 _ A)) = _
      rw [fieldAutSL_blockSL, diagConj3_blockSL_zero, hα']
    have hβ1 : ∀ C, (fieldAutSL ψ 3).trans (diagConj3 a b) (blockSL K 3 2 1 (by omega) C) =
        blockSL K 3 2 1 (by omega) (((fieldAutSL ψ 2).trans (diagConj2 b 1)) C) := fun C => by
      show diagConj3 a b (fieldAutSL ψ 3 (blockSL K 3 2 1 _ C)) = _
      rw [fieldAutSL_blockSL, diagConj3_blockSL_one]
      rfl
    refine ⟨(fieldAutSL ψ 3).trans (diagConj3 a b), hβ0, map_B23_eq _ fun C => ?_,
      (fieldAutSL ψ 2).trans (diagConj2 b 1), hβ1, fun g hg => ?_⟩
    · rw [hβ1]
      exact ⟨_, rfl⟩
    · exact diagConj2_coord b 1 (fieldAutSL_coord ψ hg)
  · obtain ⟨a, b, hab⟩ := exists_diagonal_of_diag_zero G h00 h11
    have hα' : ∀ A, α A = diagConj2 a b (invTransposeSL 2 (fieldAutSL ψ 2 A)) := fun A =>
      Subtype.ext ((hcoe A).trans (hab _))
    have hβ0 : ∀ A, ((fieldAutSL ψ 3).trans (invTransposeSL 3)).trans (diagConj3 a b)
        (blockSL K 3 2 0 (by omega) A) = blockSL K 3 2 0 (by omega) (α A) := fun A => by
      show diagConj3 a b (invTransposeSL 3 (fieldAutSL ψ 3 (blockSL K 3 2 0 _ A))) = _
      rw [fieldAutSL_blockSL, invTransposeSL_blockSL, diagConj3_blockSL_zero, hα']
    have hβ1 : ∀ C, ((fieldAutSL ψ 3).trans (invTransposeSL 3)).trans (diagConj3 a b)
        (blockSL K 3 2 1 (by omega) C) = blockSL K 3 2 1 (by omega)
          ((((fieldAutSL ψ 2).trans (invTransposeSL 2)).trans (diagConj2 b 1)) C) := fun C => by
      show diagConj3 a b (invTransposeSL 3 (fieldAutSL ψ 3 (blockSL K 3 2 1 _ C))) = _
      rw [fieldAutSL_blockSL, invTransposeSL_blockSL, diagConj3_blockSL_one]
      rfl
    refine ⟨((fieldAutSL ψ 3).trans (invTransposeSL 3)).trans (diagConj3 a b), hβ0,
      map_B23_eq _ fun C => ?_,
      ((fieldAutSL ψ 2).trans (invTransposeSL 2)).trans (diagConj2 b 1), hβ1, fun g hg => ?_⟩
    · rw [hβ1]
      exact ⟨_, rfl⟩
    · exact diagConj2_coord b 1 (invTransposeSL_coord (fieldAutSL_coord ψ hg))

end CFSG.ClassicalInvolution.Q3.Q3W
