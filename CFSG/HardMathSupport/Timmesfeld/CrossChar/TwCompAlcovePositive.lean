module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcoveAffine
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KernelPosNormalize

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KernelPos
open scoped Matrix

namespace KacData

private theorem dotProduct_one_eq_height {τ : Tag} (γ : Fin τ.rank → ℤ) :
    γ ⬝ᵥ (fun _ => 1) = height γ := by
  simp [height, dotProduct]

private theorem dotProduct_Lambda {τ : Tag} (K : KacData τ) (p : ℕ) (μ γ : Fin τ.rank → ℤ) :
    γ ⬝ᵥ K.Λ p μ = K.h * (γ ⬝ᵥ μ) - p * height γ := by
  rw [KacData.Λ]
  rw [dotProduct_sub]
  rw [dotProduct_smul]
  rw [dotProduct_smul]
  simp only [smul_eq_mul]
  rw [dotProduct_one_eq_height]

variable {τ : Tag} (K : KacData τ)

theorem alcoveValue_eq_zero_iff_neg (hK : K.Facts) {p : ℕ} (hp : 0 < p) {μ : Fin τ.rank → ℤ}
    (hμ : K.IsNormal p μ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hdvd : (p : ℤ) ∣ γ ⬝ᵥ μ) :
    alcoveValue p μ γ = 0 ↔ γ ⬝ᵥ K.Λ p μ < 0 := by
  rcases hγ.nonneg_or_nonpos with hγ_nonneg | hγ_nonpos
  · have h_alc : alcoveValue p μ γ = γ ⬝ᵥ μ := by
      simp [alcoveValue, hγ_nonneg]
    rw [h_alc]
    have h_γμ_nonneg : 0 ≤ γ ⬝ᵥ μ := by
      simp only [dotProduct]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (hγ_nonneg j) (hμ.1 j)
    have h_γμ_le_θ : γ ⬝ᵥ μ ≤ K.θ ⬝ᵥ μ := by
      simp only [dotProduct]
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hK.le_θ γ hγ hγ_nonneg j) (hμ.1 j)
    have h_θμ_le_p : K.θ ⬝ᵥ μ ≤ p := hμ.2
    have h_γμ_le_p : γ ⬝ᵥ μ ≤ p := le_trans h_γμ_le_θ h_θμ_le_p
    have h_γμ_cases : γ ⬝ᵥ μ = 0 ∨ γ ⬝ᵥ μ = p := by
      rcases hdvd with ⟨k, hk⟩
      have hp_pos : (0 : ℤ) < p := by exact_mod_cast hp
      have hk_nonneg : 0 ≤ k := by nlinarith [h_γμ_nonneg, hk, hp_pos]
      have hk_le_one : k ≤ 1 := by nlinarith [h_γμ_le_p, hk, hp_pos]
      have hk_cases : k = 0 ∨ k = 1 := by omega
      rcases hk_cases with hk0 | hk1
      · left; rw [hk, hk0, mul_zero]
      · right; rw [hk, hk1, mul_one]
    have h_ht_pos : 0 < height γ := by
      rw [IsRoot.height_pos_iff hγ]
      exact hγ_nonneg
    have h_ht_le : height γ ≤ K.h - 1 := by
      have h_le_θ := hK.le_θ γ hγ hγ_nonneg
      have h_ht_le_θ : height γ ≤ height K.θ := by
        simp only [height]
        exact Finset.sum_le_sum fun j _ => h_le_θ j
      have h_h_def : K.h = 1 + height K.θ := by simp [KacData.h, height]
      linarith
    constructor
    · intro hd
      have hΛ := dotProduct_Lambda K p μ γ
      rw [hΛ, hd, mul_zero, zero_sub]
      have hp_pos : (0 : ℤ) < p := by exact_mod_cast hp
      nlinarith
    · intro hneg
      rcases h_γμ_cases with h0 | hp'
      · rw [h0]
      · exfalso
        have hΛ := dotProduct_Lambda K p μ γ
        rw [hΛ, hp'] at hneg
        have hp_pos : (0 : ℤ) < p := by exact_mod_cast hp
        nlinarith [h_ht_le]
  · have h_not_nonneg : ¬ (∀ j, 0 ≤ γ j) := by
      intro h
      have h_zero : γ = 0 := by
        funext j
        exact le_antisymm (hγ_nonpos j) (h j)
      exact hγ.ne_zero h_zero
    have h_alc : alcoveValue p μ γ = γ ⬝ᵥ μ + p := by
      simp [alcoveValue, h_not_nonneg]
    rw [h_alc]
    have h_γμ_nonpos : γ ⬝ᵥ μ ≤ 0 := by
      simp only [dotProduct]
      exact Finset.sum_nonpos fun j _ => mul_nonpos_of_nonpos_of_nonneg (hγ_nonpos j) (hμ.1 j)
    have h_γμ_ge_neg_p : -p ≤ γ ⬝ᵥ μ := by
      have h_neg_nonneg : ∀ j, 0 ≤ (-γ) j := fun j => by simp only [Pi.neg_apply, neg_nonneg]; exact hγ_nonpos j
      have h_neg_le_θ : ∀ j, (-γ) j ≤ K.θ j := by
        intro j
        exact hK.le_θ (-γ) (IsRoot.neg hγ) h_neg_nonneg j
      have h_neg_mu : (-γ) ⬝ᵥ μ ≤ K.θ ⬝ᵥ μ := by
        simp only [dotProduct]
        exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (h_neg_le_θ j) (hμ.1 j)
      have h_mu_theta : K.θ ⬝ᵥ μ ≤ p := hμ.2
      have h_neg_mu_p : (-γ) ⬝ᵥ μ ≤ p := le_trans h_neg_mu h_mu_theta
      have h_neg_dot : (-γ) ⬝ᵥ μ = -(γ ⬝ᵥ μ) := by
        simp only [dotProduct, Pi.neg_apply, Finset.sum_neg_distrib, neg_mul]
      rw [h_neg_dot] at h_neg_mu_p
      linarith
    have h_γμ_cases : γ ⬝ᵥ μ = -p ∨ γ ⬝ᵥ μ = 0 := by
      rcases hdvd with ⟨k, hk⟩
      have hp_pos : (0 : ℤ) < p := by exact_mod_cast hp
      have hk_nonpos : k ≤ 0 := by nlinarith [h_γμ_nonpos, hk, hp_pos]
      have hk_ge_neg_one : -1 ≤ k := by nlinarith [h_γμ_ge_neg_p, hk, hp_pos]
      have hk_cases : k = -1 ∨ k = 0 := by omega
      rcases hk_cases with hk_neg1 | hk0
      · left; rw [hk, hk_neg1]; ring
      · right; rw [hk, hk0, mul_zero]
    have h_ht_neg : height γ < 0 := by
      rw [IsRoot.height_neg_iff hγ]
      exact hγ_nonpos
    have h_ht_ge : -(K.h - 1) ≤ height γ := by
      have h_neg_nonneg : ∀ j, 0 ≤ (-γ) j := fun j => by simp only [Pi.neg_apply, neg_nonneg]; exact hγ_nonpos j
      have h_le_θ := hK.le_θ (-γ) (IsRoot.neg hγ) h_neg_nonneg
      have h_ht_le_θ : height (-γ) ≤ height K.θ := by
        simp only [height]
        exact Finset.sum_le_sum fun j _ => h_le_θ j
      have h_h_def : K.h = 1 + height K.θ := by simp [KacData.h, height]
      rw [height_neg] at h_ht_le_θ
      linarith
    constructor
    · intro h
      have hd : γ ⬝ᵥ μ = -p := by linarith
      have hΛ := dotProduct_Lambda K p μ γ
      rw [hΛ, hd]
      have h_sum_pos : 0 < K.h + height γ := by linarith [h_ht_ge]
      have hp_pos : (0 : ℤ) < p := by exact_mod_cast hp
      nlinarith
    · intro hneg
      rcases h_γμ_cases with h1 | h0
      · linarith
      · exfalso
        have hΛ := dotProduct_Lambda K p μ γ
        rw [hΛ, h0, mul_zero, zero_sub] at hneg
        have hp_pos : (0 : ℤ) < p := by exact_mod_cast hp
        nlinarith [h_ht_neg]

theorem exists_kernelWeyl_alcove_stable (hK : K.Facts) {p : ℕ} (hp : 0 < p)
    {μ : Fin τ.rank → ℤ} (hμ : K.IsNormal p μ) {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hχ : ∀ γ, IsRoot τ γ → (χ (Multiplicative.ofAdd γ) = 1 ↔ (p : ℤ) ∣ γ ⬝ᵥ μ))
    {x : WeylGroup τ} (hx : (fun α => x • α) '' kernelRoots χ = kernelRoots χ)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    ∃ v ∈ kernelWeylGroup χ, ∀ γ ∈ kernelRoots χ, alcoveValue p μ γ = 0 →
      alcoveValue p μ (ε • ((v⁻¹ * x) • γ)) = 0 := by
  let ℓ : (Fin τ.rank → ℤ) →+ ℤ :=
    { toFun := fun β => -(β ⬝ᵥ K.Λ p μ)
      map_zero' := by simp [zero_dotProduct]
      map_add' := fun u v => by simp [add_dotProduct]; ring }
  have hℓ_def : ∀ β, ℓ β = -(β ⬝ᵥ K.Λ p μ) := fun β => rfl
  have hℓ_ne : ∀ γ ∈ kernelRoots χ, ℓ γ ≠ 0 := by
    intro γ hγ
    have hγ_root : IsRoot τ γ := hγ.1
    have hγ_dvd : (p : ℤ) ∣ γ ⬝ᵥ μ := (hχ γ hγ_root).1 hγ.2
    have h_not_zero : γ ⬝ᵥ K.Λ p μ ≠ 0 := by
      intro hzero
      have h_alc_cases : alcoveValue p μ γ = 0 ∨ alcoveValue p μ γ = p := by
        have h_nonneg := alcoveValue_nonneg K hK hμ hγ_root
        have h_le := alcoveValue_le K hK hμ hγ_root
        have h_dvd : (p : ℤ) ∣ alcoveValue p μ γ := by
          unfold alcoveValue
          split
          · simpa using hγ_dvd
          · exact dvd_add hγ_dvd dvd_rfl
        rcases h_dvd with ⟨k, hk⟩
        have hp_pos : (0 : ℤ) < p := by exact_mod_cast hp
        have hk_nonneg : 0 ≤ k := by nlinarith [h_nonneg, hk, hp_pos]
        have hk_le_one : k ≤ 1 := by nlinarith [h_le, hk, hp_pos]
        have hk_cases : k = 0 ∨ k = 1 := by omega
        rcases hk_cases with hk0 | hk1
        · left; rw [hk, hk0, mul_zero]
        · right; rw [hk, hk1, mul_one]
      have h_neg_dvd : (p : ℤ) ∣ (-γ) ⬝ᵥ μ := by
        rw [neg_dotProduct]
        exact dvd_neg.2 hγ_dvd
      have h_neg_alc_cases : alcoveValue p μ (-γ) = 0 ∨ alcoveValue p μ (-γ) = p := by
        have h_nonneg := alcoveValue_nonneg K hK hμ (IsRoot.neg hγ_root)
        have h_le := alcoveValue_le K hK hμ (IsRoot.neg hγ_root)
        have h_dvd : (p : ℤ) ∣ alcoveValue p μ (-γ) := by
          unfold alcoveValue
          split
          · simpa using h_neg_dvd
          · exact dvd_add h_neg_dvd dvd_rfl
        rcases h_dvd with ⟨k, hk⟩
        have hp_pos : (0 : ℤ) < p := by exact_mod_cast hp
        have hk_nonneg : 0 ≤ k := by nlinarith [h_nonneg, hk, hp_pos]
        have hk_le_one : k ≤ 1 := by nlinarith [h_le, hk, hp_pos]
        have hk_cases : k = 0 ∨ k = 1 := by omega
        rcases hk_cases with hk0 | hk1
        · left; rw [hk, hk0, mul_zero]
        · right; rw [hk, hk1, mul_one]
      have h_alc_ne_zero : alcoveValue p μ γ ≠ 0 := by
        intro h
        have h_neg := (alcoveValue_eq_zero_iff_neg K hK hp hμ hγ_root hγ_dvd).1 h
        simp only [hzero] at h_neg
        exact lt_irrefl 0 h_neg
      have h_neg_alc_ne_zero : alcoveValue p μ (-γ) ≠ 0 := by
        intro h
        have h_neg := (alcoveValue_eq_zero_iff_neg K hK hp hμ (IsRoot.neg hγ_root) h_neg_dvd).1 h
        have : (-γ) ⬝ᵥ K.Λ p μ = 0 := by rw [neg_dotProduct, hzero, neg_zero]
        simp only [this] at h_neg
        exact lt_irrefl 0 h_neg
      have h_alc_eq_p : alcoveValue p μ γ = p := by
        rcases h_alc_cases with h0 | hp'
        · exact absurd h0 h_alc_ne_zero
        · exact hp'
      have h_neg_alc_eq_p : alcoveValue p μ (-γ) = p := by
        rcases h_neg_alc_cases with h0 | hp'
        · exact absurd h0 h_neg_alc_ne_zero
        · exact hp'
      have h_add := alcoveValue_add_neg p μ hγ_root
      have hp_pos : (0 : ℤ) < p := by exact_mod_cast hp
      linarith
    rw [hℓ_def]
    exact neg_ne_zero.mpr h_not_zero
  obtain ⟨ρ₁, hρ₁_mem, hρ₁_pos⟩ := exists_kernelWeyl_smul_pos ℓ hℓ_ne
  let ℓ₂ : (Fin τ.rank → ℤ) →+ ℤ :=
    { toFun := fun β => ℓ (ε • (x⁻¹ • β))
      map_zero' := by simp
      map_add' := fun u v => by simp [smul_add, smul_add, map_add] }
  have hℓ₂_def : ∀ β, ℓ₂ β = ℓ (ε • (x⁻¹ • β)) := fun β => rfl
  have hℓ₂_ne : ∀ γ ∈ kernelRoots χ, ℓ₂ γ ≠ 0 := by
    intro γ hγ
    rw [hℓ₂_def]
    have h_xinv_mem : x⁻¹ • γ ∈ kernelRoots χ := by
      have h_image : x • (x⁻¹ • γ) = γ := by simp
      have h_mem : γ ∈ (fun α => x • α) '' kernelRoots χ := by
        rw [hx]
        exact hγ
      rcases h_mem with ⟨α, hα_mem, hα_eq⟩
      have h_eq : x • (x⁻¹ • γ) = x • α := by
        rw [h_image]
        simp only [hα_eq]
      have h_cancel : x⁻¹ • γ = α := by
        have := congrArg (fun w => x⁻¹ • w) h_eq
        simpa using this
      rw [h_cancel]
      exact hα_mem
    have h_eps_mem : ε • (x⁻¹ • γ) ∈ kernelRoots χ := by
      rcases hε with rfl | rfl
      · simpa using h_xinv_mem
      · simpa using neg_mem_kernelRoots h_xinv_mem
    exact hℓ_ne _ h_eps_mem
  obtain ⟨ρ₂, hρ₂_mem, hρ₂_pos⟩ := exists_kernelWeyl_smul_pos ℓ₂ hℓ₂_ne
  let v := ρ₂ * ρ₁⁻¹
  have hv_mem : v ∈ kernelWeylGroup χ := mul_mem hρ₂_mem (inv_mem hρ₁_mem)
  refine ⟨v, hv_mem, ?_⟩
  intro γ hγ hγ_alc
  let β := ρ₂⁻¹ • (ε • (x • γ))
  have hβ_mem : β ∈ kernelRoots χ := by
    have h_x_mem : x • γ ∈ kernelRoots χ := by
      have h_mem : x • γ ∈ (fun α => x • α) '' kernelRoots χ := Set.mem_image_of_mem _ hγ
      rwa [hx] at h_mem
    have h_eps_x_mem : ε • (x • γ) ∈ kernelRoots χ := by
      rcases hε with rfl | rfl
      · simpa using h_x_mem
      · simpa using neg_mem_kernelRoots h_x_mem
    have hρ₂inv_mem : ρ₂⁻¹ ∈ kernelWeylGroup χ := inv_mem hρ₂_mem
    exact smul_mem_kernelRoots (kernelWeylGroup_le hρ₂inv_mem) h_eps_x_mem
  have hβ_pos : β ∈ posRoots (kernelRoots χ) := by
    by_contra hβ_not_pos
    have hβ_not_pos_height : ¬0 < height β := by
      intro h
      exact hβ_not_pos ⟨hβ_mem, h⟩
    have h_negβ_pos : -β ∈ posRoots (kernelRoots χ) := mem_posRoots_of_neg hβ_mem hβ_not_pos_height
    have h_rho2_neg : 0 < ℓ₂ (ρ₂ • (-β)) := hρ₂_pos (-β) h_negβ_pos
    rw [hℓ₂_def] at h_rho2_neg
    have h_rho2_beta : ρ₂ • (-β) = -ε • (x • γ) := by
      simp only [β, smul_neg, smul_smul, mul_inv_cancel, one_smul]
      simp [neg_smul]
    rw [h_rho2_beta] at h_rho2_neg
    have h_eps_xinv : ε • (x⁻¹ • (-ε • (x • γ))) = -γ := by
      rcases hε with rfl | rfl
      · simp only [one_smul]
        simp
      · simp only [neg_one_smul]
        simp
    rw [h_eps_xinv] at h_rho2_neg
    have h_neg_gamma_lt : γ ⬝ᵥ K.Λ p μ < 0 :=
      (alcoveValue_eq_zero_iff_neg K hK hp hμ hγ.1 ((hχ γ hγ.1).1 hγ.2)).1 hγ_alc
    have h_ell_neg : ℓ (-γ) = γ ⬝ᵥ K.Λ p μ := by
      rw [hℓ_def]
      rw [neg_dotProduct]
      simp
    rw [h_ell_neg] at h_rho2_neg
    linarith
  have h_rho1_beta : 0 < ℓ (ρ₁ • β) := hρ₁_pos β hβ_pos
  have h_rho1_beta_eq : ρ₁ • β = ε • ((v⁻¹ * x) • γ) := by
    simp only [β, v]
    rw [smul_smul]
    rw [mul_inv_rev, inv_inv]
    rcases hε with rfl | rfl
    · simp only [one_smul, smul_smul]
    · simp only [neg_one_smul, smul_neg, smul_smul]
  rw [h_rho1_beta_eq] at h_rho1_beta
  rw [hℓ_def] at h_rho1_beta
  have h_dot_neg : (ε • ((v⁻¹ * x) • γ)) ⬝ᵥ K.Λ p μ < 0 := by linarith
  have h_root : IsRoot τ (ε • ((v⁻¹ * x) • γ)) := by
    have h_x_mem : x • γ ∈ kernelRoots χ := by
      have h_mem : x • γ ∈ (fun α => x • α) '' kernelRoots χ := Set.mem_image_of_mem _ hγ
      rwa [hx] at h_mem
    have h_vx_mem : (v⁻¹ * x) • γ ∈ kernelRoots χ := by
      have hv_inv_mem : v⁻¹ ∈ kernelWeylGroup χ := inv_mem hv_mem
      have hv_inv_char : v⁻¹ ∈ charStabilizer χ := kernelWeylGroup_le hv_inv_mem
      rw [mul_smul]
      exact smul_mem_kernelRoots hv_inv_char h_x_mem
    have h_eps_mem : ε • ((v⁻¹ * x) • γ) ∈ kernelRoots χ := by
      rcases hε with rfl | rfl
      · simpa using h_vx_mem
      · simpa using neg_mem_kernelRoots h_vx_mem
    exact h_eps_mem.1
  have h_dvd : (p : ℤ) ∣ (ε • ((v⁻¹ * x) • γ)) ⬝ᵥ μ := by
    have h_x_mem : x • γ ∈ kernelRoots χ := by
      have h_mem : x • γ ∈ (fun α => x • α) '' kernelRoots χ := Set.mem_image_of_mem _ hγ
      rwa [hx] at h_mem
    have h_vx_mem : (v⁻¹ * x) • γ ∈ kernelRoots χ := by
      have hv_inv_mem : v⁻¹ ∈ kernelWeylGroup χ := inv_mem hv_mem
      have hv_inv_char : v⁻¹ ∈ charStabilizer χ := kernelWeylGroup_le hv_inv_mem
      rw [mul_smul]
      exact smul_mem_kernelRoots hv_inv_char h_x_mem
    have h_eps_mem : ε • ((v⁻¹ * x) • γ) ∈ kernelRoots χ := by
      rcases hε with rfl | rfl
      · simpa using h_vx_mem
      · simpa using neg_mem_kernelRoots h_vx_mem
    exact (hχ _ h_eps_mem.1).1 h_eps_mem.2
  exact (alcoveValue_eq_zero_iff_neg K hK hp hμ h_root h_dvd).2 h_dot_neg

end KacData

end CFSG.HardMathSupport.Timmesfeld.CrossChar

end
