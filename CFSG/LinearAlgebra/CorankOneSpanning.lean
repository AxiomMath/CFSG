module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.FieldTheory.Minpoly.Field

public section

namespace CFSG.LinearAlgebra

open Matrix Polynomial

variable {k : Type*} [Field k] {d : ℕ}

theorem eq_smul_of_mulVec_eq_zero_of_rank {A : Matrix (Fin d) (Fin d) k}
    (hA : A.rank = d - 1) (hd : 1 ≤ d) {w : Fin d → k} (hw0 : w ≠ 0) (hw : A *ᵥ w = 0)
    {x : Fin d → k} (hx : A *ᵥ x = 0) : ∃ c : k, x = c • w := by
  have hker : Module.finrank k (LinearMap.ker A.mulVecLin) = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rw [Module.finrank_fin_fun] at h
    change A.rank + _ = d at h
    omega
  have hw' : (⟨w, hw⟩ : LinearMap.ker A.mulVecLin) ≠ 0 := fun h => hw0 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hw').1 hker ⟨x, hx⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

theorem corank_one_two_sided_spanning_full_algebra (hd : 2 ≤ d)
    (B : Subalgebra k (Matrix (Fin d) (Fin d) k)) (C : Matrix (Fin d) (Fin d) k) (hC : C ∈ B)
    (hrank : C.rank = d - 1) (v : Fin d → k) (hv0 : v ≠ 0) (hv : C *ᵥ v = 0)
    (u : Fin d → k) (hu0 : u ≠ 0) (hu : u ᵥ* C = 0)
    (Xs Ys : Fin d → Matrix (Fin d) (Fin d) k) (hX : ∀ i, Xs i ∈ B) (hY : ∀ j, Ys j ∈ B)
    (hXv : LinearIndependent k fun i => Xs i *ᵥ v)
    (hYu : LinearIndependent k fun j => u ᵥ* Ys j) :
    B = ⊤ := by
  classical
  have hd1 : 1 ≤ d := by omega
  have : Nontrivial (Matrix (Fin d) (Fin d) k) := by
    have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    infer_instance
  have hint : IsIntegral k C := Algebra.IsIntegral.isIntegral C
  set m := minpoly k C with hm
  have hm0 : m.coeff 0 = 0 := by
    by_contra h0
    have h1 := congrArg (aeval C) (X_mul_divX_add m)
    rw [minpoly.aeval, map_add, map_mul, aeval_X, aeval_C] at h1
    have h2 : C * ((-(m.coeff 0)⁻¹) • aeval C m.divX) = 1 := by
      rw [Matrix.mul_smul, eq_neg_of_add_eq_zero_left h1, Algebra.algebraMap_eq_smul_one,
        smul_neg, smul_smul, neg_mul, neg_smul, neg_neg, inv_mul_cancel₀ h0, one_smul]
    have hunit : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).2
      (Matrix.isUnit_det_of_right_inverse h2)
    have := C.rank_of_isUnit hunit
    rw [hrank, Fintype.card_fin] at this
    omega
  set g := m.divX with hg
  have hmg : m = X * g := by
    have h := X_mul_divX_add m
    rw [hm0, map_zero, add_zero] at h
    exact h.symm
  set J := aeval C g with hJ
  have hJB : J ∈ B :=
    (Algebra.adjoin_le (Set.singleton_subset_iff.2 hC)) (aeval_mem_adjoin_singleton k C)
  have hCJ : C * J = 0 := by
    have h := minpoly.aeval k C
    rw [← hm, hmg, map_mul, aeval_X] at h
    exact h
  have hJC : J * C = 0 := by
    have h := minpoly.aeval k C
    rw [← hm, hmg, mul_comm, map_mul, aeval_X] at h
    exact h
  have hJ0 : J ≠ 0 := by
    intro hJ0
    have hg0 : g ≠ 0 := by
      intro hg0
      have h := minpoly.ne_zero hint
      rw [← hm, hmg, hg0, mul_zero] at h
      exact h rfl
    have h1 := natDegree_le_of_dvd (minpoly.dvd k C hJ0) hg0
    rw [← hm, hmg, natDegree_X_mul hg0] at h1
    omega
  have hrankT : Cᵀ.rank = d - 1 := by rw [Matrix.rank_transpose, hrank]
  have huT : Cᵀ *ᵥ u = 0 := by rw [Matrix.mulVec_transpose]; exact hu
  have hcol : ∀ b, ∃ μ : k, ∀ a, J a b = μ * v a := fun b => by
    obtain ⟨μ, hμ⟩ := eq_smul_of_mulVec_eq_zero_of_rank hrank hd1 hv0 hv
      (x := J *ᵥ Pi.single b 1) (by rw [Matrix.mulVec_mulVec, hCJ, Matrix.zero_mulVec])
    refine ⟨μ, fun a => ?_⟩
    have h := congrFun hμ a
    rw [Matrix.mulVec_single_one, Pi.smul_apply, smul_eq_mul] at h
    exact h
  have hrow : ∀ a, ∃ ν : k, ∀ b, J a b = ν * u b := fun a => by
    obtain ⟨ν, hν⟩ := eq_smul_of_mulVec_eq_zero_of_rank hrankT hd1 hu0 huT
      (x := Jᵀ *ᵥ Pi.single a 1) (by
        rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hJC, Matrix.transpose_zero,
          Matrix.zero_mulVec])
    refine ⟨ν, fun b => ?_⟩
    have h := congrFun hν b
    rw [Matrix.mulVec_single_one, Pi.smul_apply, smul_eq_mul] at h
    exact h
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, v a₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  choose μ hμ using hcol
  obtain ⟨ν, hν⟩ := hrow a₀
  set lam := ν / v a₀ with hlam
  have hJeq : ∀ a b, J a b = lam * (v a * u b) := by
    intro a b
    have h1 : μ b * v a₀ = ν * u b := (hμ b a₀).symm.trans (hν b)
    have hμb : μ b = lam * u b := by
      rw [hlam, div_mul_eq_mul_div, eq_div_iff ha₀]
      linear_combination h1
    rw [hμ b a, hμb]
    ring
  have hlam0 : lam ≠ 0 := by
    intro h0
    apply hJ0
    ext a b
    rw [hJeq, h0, zero_mul, Matrix.zero_apply]
  have hJmat : J = lam • vecMulVec v u := by
    ext a b
    rw [hJeq, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  have hprod : ∀ i j, vecMulVec (Xs i *ᵥ v) (u ᵥ* Ys j) ∈ B := by
    intro i j
    have h1 : Xs i * J * Ys j ∈ B := mul_mem (mul_mem (hX i) hJB) (hY j)
    have h2 : Xs i * J * Ys j = lam • vecMulVec (Xs i *ᵥ v) (u ᵥ* Ys j) := by
      rw [hJmat, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    rw [h2] at h1
    have h3 := B.smul_mem h1 lam⁻¹
    rwa [smul_smul, inv_mul_cancel₀ hlam0, one_smul] at h3
  set A : Matrix (Fin d) (Fin d) k := Matrix.of fun a i => (Xs i *ᵥ v) a with hA
  set R : Matrix (Fin d) (Fin d) k := Matrix.of fun j b => (u ᵥ* Ys j) b with hR
  have hAcol : A.col = fun i => Xs i *ᵥ v := funext fun _ => funext fun _ => rfl
  have hRrow : R.row = fun j => u ᵥ* Ys j := funext fun _ => funext fun _ => rfl
  have hAu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1
    (Matrix.linearIndependent_cols_iff_isUnit.1 (by rw [hAcol]; exact hXv))
  have hRu : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).1
    (Matrix.linearIndependent_rows_iff_isUnit.1 (by rw [hRrow]; exact hYu))
  have hsingle : ∀ (i j : Fin d) (c : k),
      A * Matrix.single i j c * R = c • vecMulVec (Xs i *ᵥ v) (u ᵥ* Ys j) := by
    intro i j c
    ext a b
    simp [hA, hR, Matrix.mul_apply, Matrix.single_apply, vecMulVec_apply, ite_and]
    ring
  refine eq_top_iff.2 fun M _ => ?_
  have hM : A * (A⁻¹ * M * R⁻¹) * R = M := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hRu, Matrix.mul_one,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hAu, Matrix.one_mul]
  have hmem : A * (A⁻¹ * M * R⁻¹) * R ∈ B := by
    rw [Matrix.matrix_eq_sum_single (A⁻¹ * M * R⁻¹), Finset.mul_sum, Finset.sum_mul]
    refine Subalgebra.sum_mem _ fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Subalgebra.sum_mem _ fun j _ => ?_
    rw [hsingle]
    exact B.smul_mem (hprod i j) _
  rwa [hM] at hmem

end CFSG.LinearAlgebra
