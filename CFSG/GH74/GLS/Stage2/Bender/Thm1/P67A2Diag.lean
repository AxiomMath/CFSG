module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Matrix

section Eigen

variable {K : Type*} [Field K]

theorem three_ne_zero_of_primitive_cube_root (ω : K) (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) :
    (3 : K) ≠ 0 := by
  intro h3
  refine hω1 (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp ?_))
  linear_combination hω - ω * h3

theorem exists_eigen_decomposition_of_pow_three_eq_one (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
    (h3 : (3 : K) ≠ 0) (x : Matrix (Fin 3) (Fin 3) K) (hx : x ^ 3 = 1) (v : Fin 3 → K) :
    ∃ w₁ w₂ w₃ : Fin 3 → K, v = w₁ + w₂ + w₃ ∧ x *ᵥ w₁ = w₁ ∧ x *ᵥ w₂ = ω • w₂ ∧
      x *ᵥ w₃ = ω ^ 2 • w₃ ∧ ∀ (y : Matrix (Fin 3) (Fin 3) K) (c : K), y * x = x * y →
        y *ᵥ v = c • v → y *ᵥ w₁ = c • w₁ ∧ y *ᵥ w₂ = c • w₂ ∧ y *ᵥ w₃ = c • w₃ := by
  have hxv : x *ᵥ (x *ᵥ (x *ᵥ v)) = v := by
    rw [mulVec_mulVec, mulVec_mulVec, ← pow_three', hx, one_mulVec]
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have h3' : (3 : K)⁻¹ * 3 = 1 := inv_mul_cancel₀ h3
  refine ⟨(3 : K)⁻¹ • (v + x *ᵥ v + x *ᵥ (x *ᵥ v)),
    (3 : K)⁻¹ • (v + ω ^ 2 • x *ᵥ v + ω • x *ᵥ (x *ᵥ v)),
    (3 : K)⁻¹ • (v + ω • x *ᵥ v + ω ^ 2 • x *ᵥ (x *ᵥ v)), ?dec, ?e₁, ?e₂, ?e₃, ?comm⟩
  case dec =>
    match_scalars
    · linear_combination (-1 : K) * h3'
    · linear_combination (-(3 : K)⁻¹) * hω
    · linear_combination (-(3 : K)⁻¹) * hω
  case comm =>
    intro y c hyx hyv
    have hy1 : y *ᵥ (x *ᵥ v) = c • (x *ᵥ v) := by
      rw [mulVec_mulVec, hyx, ← mulVec_mulVec, hyv, mulVec_smul]
    have hy2 : y *ᵥ (x *ᵥ (x *ᵥ v)) = c • (x *ᵥ (x *ᵥ v)) := by
      rw [mulVec_mulVec, hyx, ← mulVec_mulVec, hy1, mulVec_smul]
    refine ⟨?_, ?_, ?_⟩ <;>
    · simp only [mulVec_smul, mulVec_add, hyv, hy1, hy2]
      module
  all_goals
    simp only [mulVec_smul, mulVec_add, hxv]
    match_scalars <;> first
      | ring1
      | linear_combination (-(3 : K)⁻¹) * hω3
      | linear_combination (-(3 : K)⁻¹ * ω) * hω3

end Eigen

section Span

variable {K : Type*} [Field K]

@[expose] def commonEigenvectors (S : Set (Matrix.SpecialLinearGroup (Fin 3) K)) :
    Set (Fin 3 → K) :=
  {v | ∀ x ∈ S, ∃ c : K, (x : Matrix (Fin 3) (Fin 3) K) *ᵥ v = c • v}

theorem commonEigenvectors_subset_span_insert (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
    (h3 : (3 : K) ≠ 0) (E : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K))
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    {S : Set (Matrix.SpecialLinearGroup (Fin 3) K)} (hS : S ⊆ E)
    {x : Matrix.SpecialLinearGroup (Fin 3) K} (hx : x ∈ E) :
    commonEigenvectors S ⊆ Submodule.span K (commonEigenvectors (insert x S)) := by
  intro v hv
  have hx3 : (x : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hE3 x hx, Matrix.SpecialLinearGroup.coe_one]
  obtain ⟨w₁, w₂, w₃, hvw, h₁, h₂, h₃, hy⟩ :=
    exists_eigen_decomposition_of_pow_three_eq_one ω hω h3 _ hx3 v
  have hmem : ∀ (w : Fin 3 → K) (c : K), (x : Matrix (Fin 3) (Fin 3) K) *ᵥ w = c • w →
      (∀ y ∈ S, ∃ c' : K, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ w = c' • w) →
      w ∈ Submodule.span K (commonEigenvectors (insert x S)) := by
    intro w c hw hSw
    refine Submodule.subset_span fun y hy => ?_
    rcases hy with rfl | hy
    · exact ⟨c, hw⟩
    · exact hSw y hy
  have hyS : ∀ y ∈ S, ∃ c' : K, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ w₁ = c' • w₁ ∧
      (y : Matrix (Fin 3) (Fin 3) K) *ᵥ w₂ = c' • w₂ ∧
      (y : Matrix (Fin 3) (Fin 3) K) *ᵥ w₃ = c' • w₃ := by
    intro y hyS
    obtain ⟨c', hc'⟩ := hv y hyS
    refine ⟨c', hy _ c' ?_ hc'⟩
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
      hcomm y (hS hyS) x hx]
  rw [hvw]
  exact add_mem (add_mem (hmem w₁ 1 (by rw [h₁, one_smul]) fun y hy => (hyS y hy).imp
    fun _ h => h.1) (hmem w₂ ω h₂ fun y hy => (hyS y hy).imp fun _ h => h.2.1))
    (hmem w₃ (ω ^ 2) h₃ fun y hy => (hyS y hy).imp fun _ h => h.2.2)

theorem top_le_span_commonEigenvectors [Finite K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
    (h3 : (3 : K) ≠ 0) (E : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K))
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    ⊤ ≤ Submodule.span K (commonEigenvectors (E : Set (Matrix.SpecialLinearGroup (Fin 3) K))) := by
  refine Set.Finite.induction_on_subset
    (motive := fun t _ => ⊤ ≤ Submodule.span K (commonEigenvectors t))
    (E : Set (Matrix.SpecialLinearGroup (Fin 3) K)) (Set.toFinite _) ?_ ?_
  · intro v _
    exact Submodule.subset_span fun x hx => absurd hx (Set.notMem_empty x)
  · intro a t ha hts _ ih
    exact ih.trans (Submodule.span_le.mpr
      (commonEigenvectors_subset_span_insert ω hω h3 E hE3 hcomm hts ha))

theorem exists_commonEigenbasis [Finite K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
    (h3 : (3 : K) ≠ 0) (E : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K))
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    ∃ b : Module.Basis (Fin 3) K (Fin 3 → K), ∀ i, ∀ x ∈ E,
      ∃ c : K, (x : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = c • b i := by
  obtain ⟨t, hts, hspan, hli⟩ := exists_linearIndependent K (commonEigenvectors
    (E : Set (Matrix.SpecialLinearGroup (Fin 3) K)))
  have htop : Submodule.span K t = ⊤ :=
    hspan.trans (top_le_iff.mp (top_le_span_commonEigenvectors ω hω h3 E hE3 hcomm))
  let B : Module.Basis t K (Fin 3 → K) :=
    Module.Basis.mk hli (by rw [Subtype.range_coe]; exact htop.ge)
  let _ : Fintype t := Fintype.ofFinite t
  let e : t ≃ Fin 3 := B.indexEquiv (Pi.basisFun K (Fin 3))
  refine ⟨B.reindex e, fun i x hx => ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
  exact hts (e.symm i).2 x hx

end Span

open scoped MatrixGroups in
theorem exists_diagonalizing_of_commuting_cube_one
    {K : Type} [Field K] [Finite K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1)
    (E : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K))
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    ∃ y : Matrix.SpecialLinearGroup (Fin 3) K, ∀ x ∈ E, ∀ i j : Fin 3, i ≠ j →
      ((y * x * y⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  obtain ⟨b, hb⟩ := exists_commonEigenbasis ω hω
    (three_ne_zero_of_primitive_cube_root ω hω hω1) E hE3 hcomm
  let A : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => b j i
  have hA : IsUnit A := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact b.linearIndependent
  have hdet : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero
  let S : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![(A.det)⁻¹, 1, 1]
  have hP : (A * S).det = 1 := by
    simp [S, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_three, hdet]
  let g : Matrix.SpecialLinearGroup (Fin 3) K := ⟨A * S, hP⟩
  have hg : (g : Matrix (Fin 3) (Fin 3) K) = A * S := rfl
  refine ⟨g⁻¹, fun x hx i j hij => ?_⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin 3 → K,
      (x : Matrix (Fin 3) (Fin 3) K) * A = A * Matrix.diagonal c := by
    choose c hc using fun j => hb j x hx
    refine ⟨c, ?_⟩
    ext i j
    have := congrFun (hc j) i
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simpa [A, Matrix.mulVec, dotProduct, mul_comm] using this
  have hxP : (x : Matrix (Fin 3) (Fin 3) K) * (A * S) = (A * S) * Matrix.diagonal c := by
    rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    simp only [mul_comm]
  rw [inv_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, hg, Matrix.mul_assoc, hxP, ← Matrix.mul_assoc,
    adjugate_mul, hP, one_smul, Matrix.one_mul, Matrix.diagonal_apply_ne _ hij]

end CFSG.GH74.GLS.Stage2.Bender.Thm1
