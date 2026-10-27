module

public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryPerfectFamily

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix Module CFSG.LieType.Universal.Unitary

variable {n : ℕ} {K : Type*} [Field K]

@[expose] noncomputable def stdHermitian (τ : K →+* K) :
    (Fin n → K) →ₛₗ[τ] (Fin n → K) →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ τ (RingHom.id K) (fun x y => ∑ i, τ (x i) * y i)
    (fun x x' y => by simp [Finset.sum_add_distrib, add_mul])
    (fun c x y => by simp [Finset.mul_sum, mul_assoc])
    (fun x y y' => by simp [Finset.sum_add_distrib, mul_add])
    (fun c x y => by simp [Finset.mul_sum, mul_left_comm])

theorem stdHermitian_apply (τ : K →+* K) (x y : Fin n → K) :
    stdHermitian τ x y = ∑ i, τ (x i) * y i :=
  rfl

theorem stdHermitian_isSymm {τ : K →+* K} (hτ : ∀ x, τ (τ x) = x) :
    (stdHermitian (n := n) τ).IsSymm := by
  refine LinearMap.isSymm_def.2 fun x y => ?_
  rw [stdHermitian_apply, stdHermitian_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hτ, mul_comm]

theorem stdHermitian_separatingLeft (τ : K →+* K) :
    (stdHermitian (n := n) τ).SeparatingLeft := by
  intro x hx
  funext i
  have h := hx (Pi.single i 1)
  rw [stdHermitian_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)] at h
  simpa using h

theorem map_transpose_mul_self_of_mem {τ : K →+* K}
    {g : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (hg : g ∈ sesqUnitaryGroup (stdHermitian τ)) :
    ((LinearMap.toMatrix' (g : (Fin n → K) →ₗ[K] (Fin n → K))).map τ)ᵀ *
      LinearMap.toMatrix' (g : (Fin n → K) →ₗ[K] (Fin n → K)) = 1 := by
  ext i j
  have h := hg (Pi.single i 1) (Pi.single j 1)
  rw [stdHermitian_apply, stdHermitian_apply] at h
  rw [Matrix.mul_apply, one_apply]
  simp only [transpose_apply, map_apply, LinearMap.toMatrix'_apply]
  rw [h]
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
    simp
  · rw [Finset.sum_eq_zero fun k _ => ?_]
    · simp [hij]
    · by_cases hk : k = i
      · subst hk
        simp [Ne.symm hij]
      · simp [hk]

theorem toLin_mem_sesqUnitaryGroup {τ : K →+* K} {M : GL (Fin n) K}
    (hM : ((M : Matrix (Fin n) (Fin n) K).map τ)ᵀ * M = 1) :
    GeneralLinearGroup.toLin M ∈ sesqUnitaryGroup (stdHermitian (n := n) τ) := by
  refine mem_sesqUnitaryGroup.2 fun v w => ?_
  rw [GeneralLinearGroup.coe_toLin, stdHermitian_apply, stdHermitian_apply]
  change (fun i => τ (((M : Matrix (Fin n) (Fin n) K) *ᵥ v) i)) ⬝ᵥ
      ((M : Matrix (Fin n) (Fin n) K) *ᵥ w) = (fun i => τ (v i)) ⬝ᵥ w
  have h : (fun i => τ (((M : Matrix (Fin n) (Fin n) K) *ᵥ v) i)) =
      ((M : Matrix (Fin n) (Fin n) K).map τ) *ᵥ fun i => τ (v i) := by
    funext i
    exact RingHom.map_mulVec τ _ v i
  rw [h, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, hM, one_mulVec]

theorem exists_fixed_perfect_even_fieldAut_dualAut {p e : ℕ} (hU : UnitaryFieldData p e K)
    (hn : 3 ≤ n) (hnq : (n, p ^ e) ≠ (3, 2)) (σ : K ≃+* K) (hσ : ∀ x, σ x = hU.bar x) :
    ∃ P : Subgroup (projectiveSL n K), Group.IsPerfect P ∧ Even (Nat.card P) ∧
      ∀ s ∈ P, (fieldAut n K σ * dualAut n K) s = s := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 + m := ⟨n - 2, by omega⟩
  set B := stdHermitian (n := 2 + m) hU.bar with hB
  have : Group.IsPerfect (sesqSpecialUnitaryGroup B) :=
    unitary_perfect hU (stdHermitian_isSymm hU.bar_bar) (stdHermitian_separatingLeft _)
      (by rw [Module.finrank_fin_fun]; exact hn) (by rwa [Module.finrank_fin_fun])
  set ρ : sesqSpecialUnitaryGroup B →* GL (Fin (2 + m)) K :=
    GeneralLinearGroup.toLin.symm.toMonoidHom.comp (sesqSpecialUnitaryGroup B).subtype with hρ
  set Q : GL (Fin 2) K := SpecialLinearGroup.toGL (QuaternionMatrices.slQuatI K) with hQ
  have hQc : (Q : Matrix (Fin 2) (Fin 2) K) = QuaternionMatrices.quatI K := rfl
  have hQ1 : ((Q : Matrix (Fin 2) (Fin 2) K).map hU.bar)ᵀ * Q = 1 := by
    rw [hQc, QuaternionMatrices.quatI]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hQmem : GeneralLinearGroup.toLin (blockGL K 2 m Q) ∈ sesqSpecialUnitaryGroup B := by
    rw [mem_sesqSpecialUnitaryGroup]
    refine ⟨toLin_mem_sesqUnitaryGroup ?_, ?_⟩
    · rw [coe_blockGL_eq_diagBlock, diagBlock_map, diagBlock_transpose, diagBlock_mul, hQ1,
        Matrix.map_one _ (map_zero _) (map_one _), transpose_one, Matrix.one_mul, diagBlock_one]
    · rw [GeneralLinearGroup.coe_toLin, ← Matrix.toLin'_apply', LinearMap.det_toLin',
        det_blockGL, hQc]
      exact QuaternionMatrices.det_quatI
  refine exists_fixed_perfect_even_of_hom ρ _ ?_ ⟨_, hQmem⟩ ?_ ?_
  · intro g hg
    have hM := map_transpose_mul_self_of_mem (sesqSpecialUnitaryGroup_le B g.2)
    rw [MulAut.mul_apply]
    refine (congrArg (fieldAut (2 + m) K σ) (dualAut_proj _)).trans
      ((fieldAut_proj σ _).trans ?_)
    congr 1
    apply Subtype.ext
    set M := LinearMap.toMatrix' ((g : LinearMap.GeneralLinearGroup K (Fin (2 + m) → K)) :
      (Fin (2 + m) → K) →ₗ[K] (Fin (2 + m) → K)) with hMdef
    have hρg : ((ρ g : GL (Fin (2 + m)) K) : Matrix (Fin (2 + m)) (Fin (2 + m)) K) = M := rfl
    have hadj : adjugate M = (M.map hU.bar)ᵀ := by
      have hdet : M.det = 1 := hρg ▸ hg
      rw [← Matrix.inv_eq_left_inv hM, Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
    change ((adjugate M)ᵀ).map σ = M
    rw [hadj, transpose_transpose]
    ext i j
    rw [map_apply, map_apply, hσ, hU.bar_bar]
  · apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← map_pow, ← map_pow, hQ, ← map_pow,
      QuaternionMatrices.slQuatI_pow_four, map_one, map_one, map_one, OneMemClass.coe_one]
  · intro c
    change ((GeneralLinearGroup.toLin.symm (GeneralLinearGroup.toLin (blockGL K 2 m Q)) :
      GL (Fin (2 + m)) K) : Matrix (Fin (2 + m)) (Fin (2 + m)) K) ≠ _
    rw [MulEquiv.symm_apply_apply]
    exact blockGL_ne_scalar_of_ne_one (by omega) toGL_slQuatI_ne_one c

section Odd

variable {K : Type} [Field K]

theorem exists_fixed_perfect_even_conjAut_fieldAut_dualAut [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hn : 3 ≤ n) (A : GL (Fin n) K)
    (σ : K ≃+* K) (hσ : σ ≠ 1) (hα : (conjAut n K A * fieldAut n K σ * dualAut n K) ^ 2 = 1) :
    ∃ P : Subgroup (projectiveSL n K), Group.IsPerfect P ∧ Even (Nat.card P) ∧
      ∀ s ∈ P, (conjAut n K A * fieldAut n K σ * dualAut n K) s = s := by
  obtain ⟨⟨e, he⟩, hσpow, H, hH⟩ :=
    odd_linear_graph_field_involution_conjugacy hp hf hK hn A σ hσ hα
  have hU : UnitaryFieldData p e K := ⟨hp, by omega, by rw [hK, he, two_mul]⟩
  refine exists_fixed_perfect_even_conj hH
    (exists_fixed_perfect_even_fieldAut_dualAut hU hn (fun h => ?_) σ fun x => ?_)
  · have h2 : p ^ e = 2 := congrArg Prod.snd h
    have hdvd : p ∣ 2 := h2 ▸ dvd_pow_self p (by omega)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd)
  · rw [UnitaryFieldData.bar_apply, hσpow, show f / 2 = e by omega]

end Odd

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
