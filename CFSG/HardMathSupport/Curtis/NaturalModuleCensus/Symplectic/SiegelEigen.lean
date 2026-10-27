module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.Basic

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

open Matrix Polynomial

variable {K : Type} [Field K]

theorem exists_eigenvector_of_pow_eq_one {p : ℕ} (hp : 0 < p) {ω : K} (hω : IsPrimitiveRoot ω p)
    {A : Matrix (Fin 2) (Fin 2) K} (hA : A ^ p = 1) :
    ∃ ζ : K, ζ ^ p = 1 ∧ ∃ u : Fin 2 → K, u ≠ 0 ∧ A *ᵥ u = ζ • u := by
  classical
  have h := X_pow_sub_one_eq_prod hp hω
  set l := (nthRootsFinset p (1 : K)).toList with hl
  have h2 : (X ^ p - 1 : K[X]) = (l.map fun ζ => (X - C ζ : K[X])).prod := by
    rw [h, hl, Finset.prod_map_toList]
  have h3 := congrArg (Polynomial.aeval A) h2
  rw [map_list_prod, List.map_map] at h3
  simp only [map_sub, map_pow, aeval_X, map_one, hA, sub_self, Function.comp_def, aeval_C] at h3
  have h4 := congrArg Matrix.det h3
  have h5 : ((l.map fun ζ => A - algebraMap K (Matrix (Fin 2) (Fin 2) K) ζ).map
      Matrix.detMonoidHom).prod = 0 := by
    rw [← map_list_prod]
    simpa using h4.symm
  rw [List.map_map, List.prod_eq_zero_iff] at h5
  obtain ⟨ζ, hζ, hdet⟩ := List.mem_map.1 h5
  have hζl : ζ ∈ nthRootsFinset p (1 : K) := by
    rw [hl] at hζ
    exact Finset.mem_toList.1 hζ
  refine ⟨ζ, (mem_nthRootsFinset hp 1).1 hζl, ?_⟩
  have hdet' : (A - algebraMap K (Matrix (Fin 2) (Fin 2) K) ζ).det = 0 := hdet
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet'
  refine ⟨u, hu0, ?_⟩
  rw [Matrix.sub_mulVec, sub_eq_zero] at hu
  rw [hu]
  simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]

theorem exists_eigenvector_inv {A : Matrix (Fin 2) (Fin 2) K} (hdet : A.det = 1) {ζ : K}
    (hζ : ζ ≠ 0) {u : Fin 2 → K} (hu0 : u ≠ 0) (hu : A *ᵥ u = ζ • u) :
    ∃ u' : Fin 2 → K, u' ≠ 0 ∧ A *ᵥ u' = ζ⁻¹ • u' := by
  have h1 : (ζ • (1 : Matrix (Fin 2) (Fin 2) K) - A).det = 0 := by
    refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨u, hu0, ?_⟩
    rw [Matrix.sub_mulVec, hu]
    simp [Matrix.smul_mulVec]
  have h2 : (ζ⁻¹ • (1 : Matrix (Fin 2) (Fin 2) K) - A).det = 0 := by
    rw [Matrix.det_fin_two] at h1 ⊢
    rw [Matrix.det_fin_two] at hdet
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.one_apply_ne,
      ne_eq, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, not_false_eq_true, smul_eq_mul, mul_zero,
      zero_sub, mul_one, one_ne_zero] at h1 ⊢
    field_simp
    linear_combination h1 + (ζ ^ 2 - 1) * hdet
  obtain ⟨u', hu', h⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h2
  refine ⟨u', hu', ?_⟩
  rw [Matrix.sub_mulVec, sub_eq_zero] at h
  rw [← h]
  simp [Matrix.smul_mulVec]

theorem exists_eigenpair [CharP K 2] {p : ℕ} (hp : 0 < p) {ω : K} (hω : IsPrimitiveRoot ω p)
    {A : Matrix (Fin 2) (Fin 2) K} (hA : A ^ p = 1) (hdet : A.det = 1)
    (hnofix : ∀ u : Fin 2 → K, u ≠ 0 → A *ᵥ u ≠ u) :
    ∃ ζ : K, ζ ^ p = 1 ∧ ζ ^ 2 ≠ 1 ∧ ∃ u u' : Fin 2 → K, u ≠ 0 ∧ u' ≠ 0 ∧ A *ᵥ u = ζ • u ∧
      A *ᵥ u' = ζ⁻¹ • u' := by
  obtain ⟨ζ, hζp, u, hu0, hu⟩ := exists_eigenvector_of_pow_eq_one hp hω hA
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne'] at hζp
    exact zero_ne_one hζp
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    exact hnofix u hu0 (by simpa using hu)
  have hζ2 : ζ ^ 2 ≠ 1 := by
    intro h
    have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
    have : (ζ - 1) ^ 2 = 0 := by linear_combination h - ζ * h2 + h2
    exact hζ1 (sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero)|>.1 this))
  obtain ⟨u', hu', hu'e⟩ := exists_eigenvector_inv hdet hζ0 hu0 hu
  exact ⟨ζ, hζp, hζ2, u, u', hu0, hu', hu, hu'e⟩

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic
