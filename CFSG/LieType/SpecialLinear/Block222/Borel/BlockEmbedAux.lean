module

public import CFSG.LieType.SpecialLinear.Block222.Borel.Aut

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

noncomputable section

variable (c : ℕ) (F : Type) [Field F]

theorem e222_rev_inl (i : Fin 2) :
    Fin.rev (e222 c (Sum.inl i)) = e222 c (Sum.inr (Sum.inr (Fin.rev i))) := by
  apply Fin.ext
  rw [Fin.val_rev]
  rw [show ((e222 c (Sum.inl i) : Fin (c + 4)) : ℕ) = (i : ℕ) by rw [e222_inl]]
  rw [show ((e222 c (Sum.inr (Sum.inr (Fin.rev i))) : Fin (c + 4)) : ℕ) =
      c + 2 + (Fin.rev i : ℕ) by rw [e222_inr_inr]]
  rw [Fin.val_rev]
  have := i.isLt
  simp
  omega

theorem e222_rev_inr_inl (i : Fin c) :
    Fin.rev (e222 c (Sum.inr (Sum.inl i))) = e222 c (Sum.inr (Sum.inl (Fin.rev i))) := by
  apply Fin.ext
  rw [Fin.val_rev]
  rw [show ((e222 c (Sum.inr (Sum.inl i)) : Fin (c + 4)) : ℕ) = (i : ℕ) + 2 by
    rw [e222_inr_inl]]
  rw [show ((e222 c (Sum.inr (Sum.inl (Fin.rev i))) : Fin (c + 4)) : ℕ) =
      (Fin.rev i : ℕ) + 2 by rw [e222_inr_inl]]
  rw [Fin.val_rev]
  have := i.isLt
  simp
  omega

theorem e222_rev_inr_inr (i : Fin 2) :
    Fin.rev (e222 c (Sum.inr (Sum.inr i))) = e222 c (Sum.inl (Fin.rev i)) := by
  apply Fin.ext
  rw [Fin.val_rev]
  rw [show ((e222 c (Sum.inr (Sum.inr i)) : Fin (c + 4)) : ℕ) = c + 2 + (i : ℕ) by
    rw [e222_inr_inr]]
  rw [show ((e222 c (Sum.inl (Fin.rev i)) : Fin (c + 4)) : ℕ) = (Fin.rev i : ℕ) by
    rw [e222_inl]]
  rw [Fin.val_rev]
  have := i.isLt
  simp
  omega

theorem reindex_blockEmbed222
    (g : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin c) F ×
      SpecialLinearGroup (Fin 2) F) :
    (Matrix.reindexAlgEquiv F F (e222 c).symm)
        ((blockEmbed222 c F g : SpecialLinearGroup (Fin (c + 4)) F) :
          Matrix (Fin (c + 4)) (Fin (c + 4)) F) =
      Matrix.fromBlocks (g.1 : Matrix (Fin 2) (Fin 2) F) 0 0
        (Matrix.fromBlocks (g.2.1 : Matrix (Fin c) (Fin c) F) 0 0
          (g.2.2 : Matrix (Fin 2) (Fin 2) F)) := by
  ext x y
  rcases x with a | (s | k) <;> rcases y with b | (t | l) <;>
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, coe_blockEmbed222_apply_inl_inl,
      coe_blockEmbed222_apply_inl_inr, coe_blockEmbed222_apply_inr_inl,
      coe_blockEmbed222_apply_inr_inl_inl, coe_blockEmbed222_apply_inr_inl_inr,
      coe_blockEmbed222_apply_inr_inr_inl, coe_blockEmbed222_apply_inr_inr_inr]

theorem reindex_borelGraph_blockEmbed222
    (g : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin c) F ×
      SpecialLinearGroup (Fin 2) F) :
    (Matrix.reindexAlgEquiv F F (e222 c).symm)
        ((borelGraph (c + 4) F (blockEmbed222 c F g) :
          SpecialLinearGroup (Fin (c + 4)) F) :
          Matrix (Fin (c + 4)) (Fin (c + 4)) F) =
      Matrix.fromBlocks (borelGraph 2 F g.2.2 : Matrix (Fin 2) (Fin 2) F) 0 0
        (Matrix.fromBlocks (borelGraph c F g.2.1 : Matrix (Fin c) (Fin c) F) 0 0
          (borelGraph 2 F g.1 : Matrix (Fin 2) (Fin 2) F)) := by
  ext x y
  rw [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]
  simp only [Equiv.symm_symm, Matrix.submatrix_apply]
  rw [coe_borelGraph_apply]
  rw [show ((blockEmbed222 c F g)⁻¹) = blockEmbed222 c F g⁻¹ from
    (map_inv (blockEmbed222 c F) g).symm]
  rcases x with a | (s | k) <;> rcases y with b | (t | l) <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      e222_rev_inl, e222_rev_inr_inl, e222_rev_inr_inr,
      coe_blockEmbed222_apply_inl_inl, coe_blockEmbed222_apply_inl_inr,
      coe_blockEmbed222_apply_inr_inl, coe_blockEmbed222_apply_inr_inl_inl,
      coe_blockEmbed222_apply_inr_inl_inr, coe_blockEmbed222_apply_inr_inr_inl,
      coe_blockEmbed222_apply_inr_inr_inr, coe_borelGraph_apply]
  all_goals rfl


section BlockCalculus

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
variable [DecidableEq ι₁] [DecidableEq ι₂]

omit [DecidableEq ι₁] [DecidableEq ι₂] in
theorem toBlocks₁₁_mul_fromBlocks_diag (A₁ : Matrix ι₁ ι₁ F)
    (A₁₂ : Matrix ι₁ ι₂ F) (A₂₂ : Matrix ι₂ ι₂ F)
    (S₁ : Matrix ι₁ ι₁ F) (S₂ : Matrix ι₂ ι₂ F)
    (A₁' : Matrix ι₁ ι₁ F) (A₁₂' : Matrix ι₁ ι₂ F) (A₂₂' : Matrix ι₂ ι₂ F) :
    (Matrix.fromBlocks A₁ A₁₂ 0 A₂₂ * Matrix.fromBlocks S₁ 0 0 S₂ *
      Matrix.fromBlocks A₁' A₁₂' 0 A₂₂').toBlocks₁₁ = A₁ * S₁ * A₁' := by
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Matrix.toBlocks_fromBlocks₁₁, Matrix.mul_assoc]

omit [DecidableEq ι₁] [DecidableEq ι₂] in
theorem toBlocks₂₂_mul_fromBlocks_diag (A₁ : Matrix ι₁ ι₁ F)
    (A₁₂ : Matrix ι₁ ι₂ F) (A₂₂ : Matrix ι₂ ι₂ F)
    (S₁ : Matrix ι₁ ι₁ F) (S₂ : Matrix ι₂ ι₂ F)
    (A₁' : Matrix ι₁ ι₁ F) (A₁₂' : Matrix ι₁ ι₂ F) (A₂₂' : Matrix ι₂ ι₂ F) :
    (Matrix.fromBlocks A₁ A₁₂ 0 A₂₂ * Matrix.fromBlocks S₁ 0 0 S₂ *
      Matrix.fromBlocks A₁' A₁₂' 0 A₂₂').toBlocks₂₂ = A₂₂ * S₂ * A₂₂' := by
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Matrix.toBlocks_fromBlocks₂₂, Matrix.mul_assoc]

theorem inv_fromBlocks_diag (Y₁ : Matrix ι₁ ι₁ F) (Y₂ : Matrix ι₂ ι₂ F)
    (Y₁' : Matrix ι₁ ι₁ F) (Y₂' : Matrix ι₂ ι₂ F)
    (h₁ : Y₁ * Y₁' = 1) (h₂ : Y₂ * Y₂' = 1) :
    (Matrix.fromBlocks Y₁ 0 0 Y₂)⁻¹ = Matrix.fromBlocks Y₁' 0 0 Y₂' :=
  Matrix.inv_eq_right_inv (by
    rw [Matrix.fromBlocks_multiply, h₁, h₂]
    simp [Matrix.fromBlocks_one])

omit [DecidableEq ι₁] [DecidableEq ι₂] in
theorem toBlocks₁₁_mul_blockDiag (Y₁ : Matrix ι₁ ι₁ F) (Y₂ : Matrix ι₂ ι₂ F)
    (X : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) F) :
    ((Matrix.fromBlocks Y₁ 0 0 Y₂) * X).toBlocks₁₁ = Y₁ * X.toBlocks₁₁ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks X]
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.toBlocks_fromBlocks₁₁]

omit [DecidableEq ι₁] [DecidableEq ι₂] in
theorem toBlocks₂₁_mul_blockDiag (Y₁ : Matrix ι₁ ι₁ F) (Y₂ : Matrix ι₂ ι₂ F)
    (X : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) F) :
    ((Matrix.fromBlocks Y₁ 0 0 Y₂) * X).toBlocks₂₁ = Y₂ * X.toBlocks₂₁ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks X]
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.toBlocks_fromBlocks₂₁]

omit [DecidableEq ι₁] [DecidableEq ι₂] in
theorem toBlocks₂₂_mul_blockDiag (Y₁ : Matrix ι₁ ι₁ F) (Y₂ : Matrix ι₂ ι₂ F)
    (X : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) F) :
    ((Matrix.fromBlocks Y₁ 0 0 Y₂) * X).toBlocks₂₂ = Y₂ * X.toBlocks₂₂ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks X]
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.toBlocks_fromBlocks₂₂]

end BlockCalculus

variable {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
  [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq ι₃]

theorem exists_fromBlocks_quotient
    (A₁ : Matrix ι₁ ι₁ F) (A₁₂ : Matrix ι₁ (ι₂ ⊕ ι₃) F)
    (A₂ : Matrix ι₂ ι₂ F) (A₂₃ : Matrix ι₂ ι₃ F) (A₃ : Matrix ι₃ ι₃ F)
    (A₁' : Matrix ι₁ ι₁ F) (A₁₂' : Matrix ι₁ (ι₂ ⊕ ι₃) F)
    (A₂' : Matrix ι₂ ι₂ F) (A₂₃' : Matrix ι₂ ι₃ F) (A₃' : Matrix ι₃ ι₃ F)
    (S₁ : Matrix ι₁ ι₁ F) (S₂ : Matrix ι₂ ι₂ F) (S₃ : Matrix ι₃ ι₃ F)
    (β₁ β₁' : Matrix ι₁ ι₁ F) (β₂ β₂' : Matrix ι₂ ι₂ F)
    (β₃ β₃' : Matrix ι₃ ι₃ F)
    (hβ₁ : β₁ = A₁ * S₁ * A₁') (hβ₂ : β₂ = A₂ * S₂ * A₂') (hβ₃ : β₃ = A₃ * S₃ * A₃')
    (hβ₁' : β₁' * β₁ = 1) (hβ₂' : β₂' * β₂ = 1) (hβ₃' : β₃' * β₃ = 1)
    (hβ₁'' : β₁ * β₁' = 1) (hβ₂'' : β₂ * β₂' = 1) (hβ₃'' : β₃ * β₃' = 1) :
    ∃ B E,
      (Matrix.fromBlocks β₁ 0 0 (Matrix.fromBlocks β₂ 0 0 β₃))⁻¹ *
        (Matrix.fromBlocks A₁ A₁₂ 0 (Matrix.fromBlocks A₂ A₂₃ 0 A₃) *
          Matrix.fromBlocks S₁ 0 0 (Matrix.fromBlocks S₂ 0 0 S₃) *
          Matrix.fromBlocks A₁' A₁₂' 0 (Matrix.fromBlocks A₂' A₂₃' 0 A₃')) =
      Matrix.fromBlocks (1 : Matrix ι₁ ι₁ F) B 0
        (Matrix.fromBlocks (1 : Matrix ι₂ ι₂ F) E 0 (1 : Matrix ι₃ ι₃ F)) := by
  let X : Matrix (ι₁ ⊕ (ι₂ ⊕ ι₃)) (ι₁ ⊕ (ι₂ ⊕ ι₃)) F :=
    Matrix.fromBlocks A₁ A₁₂ 0 (Matrix.fromBlocks A₂ A₂₃ 0 A₃) *
      Matrix.fromBlocks S₁ 0 0 (Matrix.fromBlocks S₂ 0 0 S₃) *
      Matrix.fromBlocks A₁' A₁₂' 0 (Matrix.fromBlocks A₂' A₂₃' 0 A₃')
  let Z : Matrix (ι₁ ⊕ (ι₂ ⊕ ι₃)) (ι₁ ⊕ (ι₂ ⊕ ι₃)) F :=
    (Matrix.fromBlocks β₁ 0 0 (Matrix.fromBlocks β₂ 0 0 β₃))⁻¹ * X
  have hYinv : (Matrix.fromBlocks β₁ 0 0 (Matrix.fromBlocks β₂ 0 0 β₃))⁻¹ =
      Matrix.fromBlocks β₁' 0 0 (Matrix.fromBlocks β₂' 0 0 β₃') := by
    apply inv_fromBlocks_diag
    · exact hβ₁''
    · rw [Matrix.fromBlocks_multiply, hβ₂'', hβ₃'']
      simp [Matrix.fromBlocks_one]
  have hX₁₁ : X.toBlocks₁₁ = A₁ * S₁ * A₁' := by
    simp only [X]
    exact toBlocks₁₁_mul_fromBlocks_diag (F := F) A₁ A₁₂ _ S₁ _ A₁' A₁₂' _
  have hX₂₁ : X.toBlocks₂₁ = 0 := by
    simp only [X]
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [Matrix.toBlocks_fromBlocks₂₁]
  have hX₂₂ : X.toBlocks₂₂ =
      Matrix.fromBlocks A₂ A₂₃ 0 A₃ * Matrix.fromBlocks S₂ 0 0 S₃ *
        Matrix.fromBlocks A₂' A₂₃' 0 A₃' := by
    simp only [X]
    exact toBlocks₂₂_mul_fromBlocks_diag (F := F) A₁ A₁₂ _ S₁ _ A₁' A₁₂' _
  have hX₂₂₁₁ : X.toBlocks₂₂.toBlocks₁₁ = A₂ * S₂ * A₂' := by
    rw [hX₂₂]
    exact toBlocks₁₁_mul_fromBlocks_diag (F := F) A₂ A₂₃ A₃ S₂ S₃ A₂' A₂₃' A₃'
  have hX₂₂₂₁ : X.toBlocks₂₂.toBlocks₂₁ = 0 := by
    rw [hX₂₂]
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [Matrix.toBlocks_fromBlocks₂₁]
  have hX₂₂₂₂ : X.toBlocks₂₂.toBlocks₂₂ = A₃ * S₃ * A₃' := by
    rw [hX₂₂]
    exact toBlocks₂₂_mul_fromBlocks_diag (F := F) A₂ A₂₃ A₃ S₂ S₃ A₂' A₂₃' A₃'
  have hZ₁₁ : Z.toBlocks₁₁ = 1 := by
    simp only [Z]
    rw [hYinv, toBlocks₁₁_mul_blockDiag (F := F), hX₁₁, ← hβ₁]
    exact hβ₁'
  have hZ₂₁ : Z.toBlocks₂₁ = 0 := by
    simp only [Z]
    rw [hYinv, toBlocks₂₁_mul_blockDiag (F := F), hX₂₁, Matrix.mul_zero]
  have hZ₂₂ : Z.toBlocks₂₂ =
      Matrix.fromBlocks β₂' 0 0 β₃' * X.toBlocks₂₂ := by
    simp only [Z]
    rw [hYinv, toBlocks₂₂_mul_blockDiag (F := F)]
  have hZ₂₂₁₁ : Z.toBlocks₂₂.toBlocks₁₁ = 1 := by
    rw [hZ₂₂, toBlocks₁₁_mul_blockDiag (F := F), hX₂₂₁₁, ← hβ₂]
    exact hβ₂'
  have hZ₂₂₂₁ : Z.toBlocks₂₂.toBlocks₂₁ = 0 := by
    rw [hZ₂₂, toBlocks₂₁_mul_blockDiag (F := F), hX₂₂₂₁, Matrix.mul_zero]
  have hZ₂₂₂₂ : Z.toBlocks₂₂.toBlocks₂₂ = 1 := by
    rw [hZ₂₂, toBlocks₂₂_mul_blockDiag (F := F), hX₂₂₂₂, ← hβ₃]
    exact hβ₃'
  refine ⟨Z.toBlocks₁₂, Z.toBlocks₂₂.toBlocks₁₂, ?_⟩
  change Z = Matrix.fromBlocks (1 : Matrix ι₁ ι₁ F) Z.toBlocks₁₂ 0
    (Matrix.fromBlocks (1 : Matrix ι₂ ι₂ F) Z.toBlocks₂₂.toBlocks₁₂ 0
      (1 : Matrix ι₃ ι₃ F))
  rw [← Matrix.fromBlocks_toBlocks Z, Matrix.fromBlocks_inj]
  refine ⟨hZ₁₁, rfl, hZ₂₁, ?_⟩
  rw [← Matrix.fromBlocks_toBlocks Z.toBlocks₂₂, Matrix.fromBlocks_inj]
  exact ⟨hZ₂₂₁₁, rfl, hZ₂₂₂₁, hZ₂₂₂₂⟩


end

end CFSG.LieType.SpecialLinear
