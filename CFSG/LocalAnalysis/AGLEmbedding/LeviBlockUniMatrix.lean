module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

namespace CFSG.AGLEmbedding.LeviBlock

open Matrix

variable {ι ι' κ R : Type*} {φ : ι → κ} (hφ : Function.Injective φ)

open scoped Classical in
@[expose] noncomputable def extendEquiv : κ ≃ ι ⊕ {x // x ∉ Set.range φ} :=
  (Equiv.sumCompl (· ∈ Set.range φ)).symm.trans
    (Equiv.sumCongr (Equiv.ofInjective φ hφ).symm (Equiv.refl _))

theorem extendEquiv_apply_map (i : ι) : extendEquiv hφ (φ i) = Sum.inl i := by
  classical
  rw [extendEquiv, Equiv.trans_apply]
  convert congrArg (Equiv.sumCongr (Equiv.ofInjective φ hφ).symm (Equiv.refl _))
    (Equiv.sumCompl_symm_apply_of_pos (p := (· ∈ Set.range φ)) (Set.mem_range_self i))
  simp

theorem extendEquiv_apply_of_not_mem {x : κ} (hx : x ∉ Set.range φ) :
    extendEquiv hφ x = Sum.inr ⟨x, hx⟩ := by
  classical
  rw [extendEquiv, Equiv.trans_apply]
  convert congrArg (Equiv.sumCongr (Equiv.ofInjective φ hφ).symm (Equiv.refl _))
    (Equiv.sumCompl_symm_apply_of_neg (p := (· ∈ Set.range φ)) hx)
  rfl

variable [DecidableEq κ]

@[expose] noncomputable def extendMat [Zero R] [One R] (B : Matrix ι ι R) : Matrix κ κ R :=
  (fromBlocks B 0 0 1).submatrix (extendEquiv hφ) (extendEquiv hφ)

theorem extendMat_apply_map [Zero R] [One R] (B : Matrix ι ι R) (i j : ι) :
    extendMat hφ B (φ i) (φ j) = B i j := by
  rw [extendMat, submatrix_apply, extendEquiv_apply_map, extendEquiv_apply_map,
    fromBlocks_apply₁₁]

theorem extendMat_apply_of_not_mem [Zero R] [One R] (B : Matrix ι ι R) {x y : κ}
    (h : x ∉ Set.range φ ∨ y ∉ Set.range φ) : extendMat hφ B x y = (1 : Matrix κ κ R) x y := by
  rw [extendMat, submatrix_apply]
  by_cases hx : x ∈ Set.range φ <;> by_cases hy : y ∈ Set.range φ
  · exact absurd (h.elim (absurd hx) (absurd hy)) id
  · obtain ⟨i, rfl⟩ := hx
    rw [extendEquiv_apply_map, extendEquiv_apply_of_not_mem hφ hy, fromBlocks_apply₁₂,
      Matrix.zero_apply, one_apply_ne fun h' => hy ⟨i, h'⟩]
  · obtain ⟨j, rfl⟩ := hy
    rw [extendEquiv_apply_of_not_mem hφ hx, extendEquiv_apply_map, fromBlocks_apply₂₁,
      Matrix.zero_apply, one_apply_ne fun h' => hx ⟨j, h'.symm⟩]
  · rw [extendEquiv_apply_of_not_mem hφ hx, extendEquiv_apply_of_not_mem hφ hy,
      fromBlocks_apply₂₂]
    by_cases hxy : x = y
    · subst hxy
      simp
    · rw [one_apply_ne hxy, one_apply_ne fun h' => hxy (congrArg Subtype.val h')]

theorem extendMat_mul [Fintype ι] [Fintype κ] [Semiring R] (B B' : Matrix ι ι R) :
    extendMat hφ (B * B') = extendMat hφ B * extendMat hφ B' := by
  classical
  rw [extendMat, extendMat, extendMat, submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem extendMat_one [DecidableEq ι] [Zero R] [One R] :
    extendMat hφ (1 : Matrix ι ι R) = 1 := by
  rw [extendMat, fromBlocks_one, submatrix_one_equiv]

theorem det_extendMat [Fintype ι] [Fintype κ] [DecidableEq ι] [CommRing R] (B : Matrix ι ι R) :
    (extendMat hφ B).det = B.det := by
  classical
  rw [extendMat, det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, mul_one]

theorem extendMat_transpose [Zero R] [One R] (B : Matrix ι ι R) :
    (extendMat hφ B)ᵀ = extendMat hφ Bᵀ := by
  rw [extendMat, extendMat, transpose_submatrix, fromBlocks_transpose, transpose_one]
  simp only [transpose_zero]

theorem extendMat_map {S : Type*} [Semiring R] [Semiring S] (g : R →+* S) (B : Matrix ι ι R) :
    (extendMat hφ B).map g = extendMat hφ (B.map g) := by
  rw [extendMat, extendMat, ← submatrix_map, fromBlocks_map, Matrix.map_zero _ (map_zero g),
    Matrix.map_zero _ (map_zero g), Matrix.map_one _ (map_zero g) (map_one g)]

theorem extendMat_inv [Fintype ι] [Fintype κ] [DecidableEq ι] [CommRing R] {B : Matrix ι ι R}
    (hB : IsUnit B.det) : (extendMat hφ B)⁻¹ = extendMat hφ B⁻¹ :=
  inv_eq_right_inv (by rw [← extendMat_mul, mul_nonsing_inv _ hB, extendMat_one])

theorem submatrix_extendMat [Zero R] [One R] (B : Matrix ι ι R) :
    (extendMat hφ B).submatrix φ φ = B :=
  Matrix.ext fun i j => extendMat_apply_map hφ B i j

theorem submatrix_extendMat_of_disjoint [Zero R] [One R] [DecidableEq ι'] {ψ : ι' → κ}
    (hψ : Function.Injective ψ) (hd : ∀ i j, ψ i ≠ φ j) (B : Matrix ι ι R) :
    (extendMat hφ B).submatrix ψ ψ = 1 := by
  ext i j
  rw [submatrix_apply, extendMat_apply_of_not_mem hφ B (Or.inl fun ⟨k, hk⟩ => hd i k hk.symm)]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [one_apply_ne (hψ.ne hij), one_apply_ne hij]

omit [DecidableEq κ] in
include hφ in
theorem submatrix_mul_of_cuts [Fintype ι] [Fintype κ] [Semiring R] {pos : κ → ℕ} {a b : ℕ}
    (hrange : ∀ x, x ∈ Set.range φ ↔ a ≤ pos x ∧ pos x < b) {M N : Matrix κ κ R}
    (hM : ∀ u w, pos w < a → a ≤ pos u → M u w = 0)
    (hN : ∀ u w, pos w < b → b ≤ pos u → N u w = 0) :
    (M * N).submatrix φ φ = M.submatrix φ φ * N.submatrix φ φ := by
  ext i j
  simp only [submatrix_apply, mul_apply]
  symm
  refine Fintype.sum_of_injective φ hφ _ _ (fun w hw => ?_) fun _ => rfl
  rw [hrange, not_and_or, not_le, not_lt] at hw
  have hi := (hrange (φ i)).mp ⟨i, rfl⟩
  have hj := (hrange (φ j)).mp ⟨j, rfl⟩
  rcases hw with hw | hw
  · rw [hM _ _ hw hi.1, zero_mul]
  · rw [hN _ _ hj.2 hw, mul_zero]

end CFSG.AGLEmbedding.LeviBlock
