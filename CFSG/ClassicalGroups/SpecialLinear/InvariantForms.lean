module

public import CFSG.ClassicalGroups.SpecialLinear.Transitive

public section

namespace CFSG.ClassicalGroups.SpecialLinear

open CFSG.Open Matrix

private theorem transpose_mulVec_dotProduct_eq {K : Type} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (v w : Fin n → K) :
    (Mᵀ *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (M *ᵥ w) := by
  rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]

private theorem vec_eq_of_forall_dotProduct_eq {K : Type} [Field K] {n : ℕ}
    {u v : Fin n → K} (h : ∀ w : Fin n → K, u ⬝ᵥ w = v ⬝ᵥ w) : u = v := by
  funext i
  simpa using h (Pi.single i 1)

private theorem pairing_basis_eq_zero {K : Type} [Field K] {n : ℕ} (hn : 2 ≤ n)
    {A : Type*} [AddCommGroup A] (f : (Fin n → K) →+ (Fin n → K) →+ A)
    (hf : ∀ g ∈ StatedSL n K, ∀ x γ : Fin n → K,
      f ((g : Matrix (Fin n) (Fin n) K) *ᵥ x)
        (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ γ) = f x γ)
    (i₀ : Fin n) {δ : Fin n → K} (hδ : δ ⬝ᵥ Pi.single i₀ (1 : K) = 0) :
    f (Pi.single i₀ (1 : K)) δ = 0 := by
  by_cases hδ0 : δ = 0
  · subst hδ0
    simp
  obtain ⟨j, hj⟩ : ∃ j, δ j ≠ 0 := by
    by_contra h
    push Not at h
    exact hδ0 (funext h)
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨k, hkj⟩ := exists_ne j
  obtain ⟨c, hc⟩ : ∃ c : Fin n → K, c = Pi.single k 1 - (δ k / δ j) • Pi.single j 1 :=
    ⟨_, rfl⟩
  have hck : c k = 1 := by
    simp [hc, Pi.single_apply, hkj]
  have hδc : δ ⬝ᵥ c = 0 := by
    simp [hc, dotProduct_sub, dotProduct_smul, hj]
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K (Fin n → K), ∀ z, φ z = δ ⬝ᵥ z :=
    ⟨{ toFun := fun z => δ ⬝ᵥ z
       map_add' := fun a b => by simp [dotProduct_add]
       map_smul' := fun r a => by simp [dotProduct_smul] }, fun z => rfl⟩
  obtain ⟨g, hg, hgz⟩ :=
    exists_statedSL_mulVec_eq_transvection (v := c) φ (by rw [hφ]; exact hδc)
  simp only [hφ] at hgz
  have hg0 : (g : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i₀ (1 : K) = Pi.single i₀ 1 := by
    rw [hgz, hδ, zero_smul, add_zero]
  have hginv : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i₀ (1 : K) =
      Pi.single i₀ 1 := by
    calc ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i₀ (1 : K)
        = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
            ((g : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i₀ (1 : K)) := by rw [hg0]
      _ = Pi.single i₀ 1 := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
  have hgT : (g : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ Pi.single k (1 : K) = Pi.single k 1 + δ := by
    refine vec_eq_of_forall_dotProduct_eq fun w => ?_
    rw [transpose_mulVec_dotProduct_eq, hgz]
    simp [hck, dotProduct_add, dotProduct_smul, add_dotProduct]
  have h := hf g⁻¹ (inv_mem hg) (Pi.single i₀ (1 : K)) (Pi.single k 1)
  rw [inv_inv, hginv, hgT, map_add] at h
  simpa using h

theorem pairing_eq_zero_of_statedSL_invariant {K : Type} [Field K] {n : ℕ} (hn : 2 ≤ n)
    {A : Type*} [AddCommGroup A] (f : (Fin n → K) →+ (Fin n → K) →+ A)
    (hf : ∀ g ∈ StatedSL n K, ∀ x γ : Fin n → K,
      f ((g : Matrix (Fin n) (Fin n) K) *ᵥ x)
        (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ γ) = f x γ)
    {x γ : Fin n → K} (hxγ : γ ⬝ᵥ x = 0) : f x γ = 0 := by
  by_cases hx : x = 0
  · subst hx
    simp
  have hn2 : 2 ≤ n := by omega
  set i₀ : Fin n := ⟨0, by omega⟩
  have he0 : (Pi.single i₀ (1 : K) : Fin n → K) ≠ 0 :=
    Pi.single_ne_zero_iff.mpr one_ne_zero
  obtain ⟨A₀, hA₀, hA₀x⟩ := exists_statedSL_mulVec_eq hn2 hx he0
  have hδ : ((((A₀⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ γ) ⬝ᵥ
      Pi.single i₀ (1 : K)) = 0 := by
    rw [← hA₀x, transpose_mulVec_dotProduct_eq, Matrix.mulVec_mulVec, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    exact hxγ
  have key := pairing_basis_eq_zero hn2 f hf i₀ hδ
  have h := hf A₀ hA₀ x γ
  rw [hA₀x] at h
  exact h.symm.trans key

end CFSG.ClassicalGroups.SpecialLinear
