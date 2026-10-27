module

public import CFSG.CGT.Timmesfeld75.ListWCLinBasic

public section

namespace CFSG.ClassicalGroups.SpecialLinear

open Matrix
open scoped MatrixGroups

theorem exists_conj_transvSL_eq {K : Type*} [Field K]
    {v w : Fin 3 → K} (hvw : w ⬝ᵥ v = 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ W : SpecialLinearGroup (Fin 3) K,
      W * CFSG.CGT.Timmesfeld75.tvSL (c := v) (a := w) hvw * W⁻¹ =
        CFSG.CGT.Timmesfeld75.tvSL (c := Pi.single 0 1) (a := Pi.single 1 1) (by
          rw [dotProduct]
          refine Finset.sum_eq_zero ?_
          intro i _
          by_cases hi : i = 1
          · subst hi
            simp
          · rw [Pi.single_eq_of_ne hi]
            simp) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, w j ≠ 0 := Function.ne_iff.mp hw
  let z : Fin 3 → K := Pi.single j (w j)⁻¹
  have hz : w ⬝ᵥ z = 1 := by
    dsimp only [z]
    rw [dotProduct_single]
    exact mul_inv_cancel₀ hj
  let φ : (Fin 3 → K) →ₗ[K] K :=
    { toFun := fun x => w ⬝ᵥ x
      map_add' := fun x y => by simp [dotProduct_add]
      map_smul' := fun a x => by simp [dotProduct_smul] }
  have hφ_ne : φ ≠ 0 := by
    intro h
    have h1 := congrArg (fun f : (Fin 3 → K) →ₗ[K] K => f (Pi.single j 1)) h
    simp [φ] at h1
    exact hj h1
  have hker_finrank : Module.finrank K (LinearMap.ker φ) = 2 := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero (f := φ) hφ_ne
    have h3 : Module.finrank K (Fin 3 → K) = 3 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    omega
  have hspan_le : Submodule.span K {v} ≤ LinearMap.ker φ := by
    intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [LinearMap.mem_ker]
    simp [φ, hvw]
  have hspan_ne : Submodule.span K {v} ≠ LinearMap.ker φ := by
    intro h
    have h1 : Module.finrank K (Submodule.span K {v}) = 1 := finrank_span_singleton hv
    have h2 : Module.finrank K (LinearMap.ker φ) = 2 := hker_finrank
    rw [← h, h1] at h2
    omega
  have hlt : Submodule.span K {v} < LinearMap.ker φ := lt_of_le_of_ne hspan_le hspan_ne
  obtain ⟨u, hu_ker, hu_span⟩ := IsConcreteLE.exists_of_lt hlt
  have hwu : w ⬝ᵥ u = 0 := by
    simpa [φ] using hu_ker
  have hvu : LinearIndependent K ![v, u] := by
    rw [LinearIndependent.pair_iff' hv]
    intro a ha
    exact hu_span (Submodule.mem_span_singleton.mpr ⟨a, ha⟩)
  have hli : LinearIndependent K ![v, z, u] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
    have hφ := congrArg φ hg
    simp only [map_add, map_smul, LinearMap.map_zero] at hφ
    have hg1 : g 1 = 0 := by
      simpa [φ, hvw, hz, hwu, smul_eq_mul] using hφ
    rw [hg1, zero_smul, add_zero] at hg
    have hpair := (LinearIndependent.pair_iff.mp hvu) (g 0) (g 2) hg
    intro i
    fin_cases i <;> simp [hpair.1, hg1, hpair.2]
  let g0 : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => ![v, z, u] j i
  have hcols : LinearIndependent K (fun j => g0.col j) := by
    have hcols_eq : (fun j => g0.col j) = ![v, z, u] := by
      funext j
      ext i
      simp [g0, Matrix.col_apply]
    rw [hcols_eq]
    exact hli
  have hunit : IsUnit g0.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_cols_iff_isUnit.mp hcols)
  let d : K := g0.det
  have hd : d ≠ 0 := hunit.ne_zero
  let D : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![1, 1, d⁻¹]
  let g : Matrix (Fin 3) (Fin 3) K := g0 * D
  have hdet : g.det = 1 := by
    dsimp only [g, D]
    rw [Matrix.det_mul, Matrix.det_diagonal]
    simp [Fin.prod_univ_three, hd, d]
  have hgcol0 : ∀ i, g i 0 = v i := by
    intro i
    simp [g, g0, D, Matrix.mul_diagonal]
  have hgcol1 : ∀ i, g i 1 = z i := by
    intro i
    simp [g, g0, D, Matrix.mul_diagonal]
  have hgcol2 : ∀ i, g i 2 = d⁻¹ * u i := by
    intro i
    rw [show g i 2 = u i * d⁻¹ by simp [g, g0, D, Matrix.mul_diagonal]]
    exact mul_comm _ _
  have hcol0 : g.col 0 = v := funext hgcol0
  have hcol1 : g.col 1 = z := funext hgcol1
  have hcol2 : g.col 2 = d⁻¹ • u := by
    funext i
    rw [Matrix.col_apply, hgcol2 i, Pi.smul_apply, smul_eq_mul]
  have hge0 : g *ᵥ (Pi.single 0 1 : Fin 3 → K) = v := by
    rw [Matrix.mulVec_single_one]
    funext i
    simpa [Matrix.col_apply] using hgcol0 i
  let gUnit : SpecialLinearGroup (Fin 3) K := ⟨g, hdet⟩
  have hWv : ((gUnit⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v =
      (Pi.single 0 1 : Fin 3 → K) := by
    have h := CFSG.CGT.Timmesfeld75.inv_mulVec_mulVec' gUnit (Pi.single 0 1)
    have h' : ((gUnit : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (Pi.single 0 1 : Fin 3 → K) = v := by
      simpa [gUnit] using hge0
    rwa [h'] at h
  have hwg : w ᵥ* g = (Pi.single 1 1 : Fin 3 → K) := by
    funext j
    fin_cases j <;>
      simp [Matrix.vecMul_apply, hcol0, hcol1, hcol2, hvw, hz, hwu]
  have hstd : (Pi.single 1 1 : Fin 3 → K) ⬝ᵥ (Pi.single 0 1 : Fin 3 → K) = 0 := by
    rw [dotProduct]
    refine Finset.sum_eq_zero ?_
    intro i _
    by_cases hi : i = 1
    · subst hi
      simp
    · rw [Pi.single_eq_of_ne hi]
      simp
  let T : SpecialLinearGroup (Fin 3) K :=
    CFSG.CGT.Timmesfeld75.tvSL (c := v) (a := w) hvw
  let T₀ : SpecialLinearGroup (Fin 3) K :=
    CFSG.CGT.Timmesfeld75.tvSL (c := Pi.single 0 1) (a := Pi.single 1 1) hstd
  refine ⟨gUnit⁻¹, ?_⟩
  apply Subtype.ext
  have hconj := CFSG.CGT.Timmesfeld75.coe_conj_of_coe (m := 3) (g := gUnit⁻¹) (x := T)
    (c := v) (a := w) (CFSG.CGT.Timmesfeld75.coe_tvSL hvw)
  have hWinv : (((gUnit⁻¹ : SpecialLinearGroup (Fin 3) K)⁻¹ :
      SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = g := by
    rw [inv_inv]
  rw [hconj, hWv, hWinv, hwg, show (T₀ : Matrix (Fin 3) (Fin 3) K) = 1 + vecMulVec
    (Pi.single 0 1 : Fin 3 → K) (Pi.single 1 1 : Fin 3 → K) from
      CFSG.CGT.Timmesfeld75.coe_tvSL hstd]

end CFSG.ClassicalGroups.SpecialLinear
