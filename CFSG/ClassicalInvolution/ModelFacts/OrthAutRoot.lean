module

public import CFSG.ClassicalInvolution.ModelFacts.OrthAutPlus

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OrthAut

variable {K X : Type*} [Group K] [Group X] {F : Type} [Field F] {p : ℕ} {W : Type}
  [AddCommGroup W] [Module F W] [Nontrivial W]

theorem sq_eq_one_of_scalar (A : K ≃* K) (hA2 : ∀ y, A (A y) = y) (f : Multiplicative W →* K)
    (hf : Function.Injective f) (χ : F) (hA : ∀ c : W, A (f (Multiplicative.ofAdd c)) =
      f (Multiplicative.ofAdd (χ • c))) : χ * χ = 1 := by
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : W)
  have h1 := hA2 (f (Multiplicative.ofAdd w₀))
  rw [hA, hA] at h1
  have h3 := Multiplicative.ofAdd.injective (hf h1)
  rw [smul_smul] at h3
  have h4 : (χ * χ - 1) • w₀ = 0 := by rw [sub_smul, h3, one_smul, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_right hw₀)

theorem normalizes_and_fixes_of_scalar
    (hZ : ∀ ζ ∈ Subgroup.center K, ζ ^ p = 1 → ζ = 1) (θ : K →* X)
    (hker : θ.ker ≤ Subgroup.center K) (σ : X ≃* X) (α A : K ≃* K) (κ : K)
    (hαθ : ∀ y, θ (α y) = σ (θ y)) (hA : ∀ y, α (κ * y * κ⁻¹) = κ * A y * κ⁻¹)
    (hA2 : ∀ y, A (A y) = y) (f₁ f₂ : Multiplicative W →* K) (hf₁ : Function.Injective f₁)
    (hp₁ : ∀ c : W, (f₁ (Multiplicative.ofAdd c)) ^ p = 1) (χ₁ χ₂ : F)
    (hA₁ : ∀ c : W, A (f₁ (Multiplicative.ofAdd c)) = f₁ (Multiplicative.ofAdd (χ₁ • c)))
    (hA₂ : ∀ c : W, A (f₂ (Multiplicative.ofAdd c)) = f₂ (Multiplicative.ofAdd (χ₂ • c)))
    (hχ : χ₁ = 1 → χ₂ = 1) :
    ((((f₁.range ⊔ f₂.range).map (MulAut.conj κ).toMonoidHom).map θ).map σ.toMonoidHom =
      ((f₁.range ⊔ f₂.range).map (MulAut.conj κ).toMonoidHom).map θ) ∧
    ((∀ y ∈ ((f₁.range ⊔ f₂.range).map (MulAut.conj κ).toMonoidHom).map θ, σ y = y) ↔
      χ₁ = 1) := by
  have hAmem : ∀ (f : Multiplicative W →* K) (χ : F),
      (∀ c : W, A (f (Multiplicative.ofAdd c)) = f (Multiplicative.ofAdd (χ • c))) →
        ∀ y ∈ f.range, A y ∈ f.range := by
    intro f χ hf
    rintro y ⟨c, rfl⟩
    rw [← ofAdd_toAdd c, hf]
    exact ⟨_, rfl⟩
  have hSA : ∀ y ∈ f₁.range ⊔ f₂.range, A y ∈ f₁.range ⊔ f₂.range := by
    have hle : f₁.range ⊔ f₂.range ≤ (f₁.range ⊔ f₂.range).comap A.toMonoidHom := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · exact Subgroup.mem_sup_left (hAmem f₁ χ₁ hA₁ y hy)
      · exact Subgroup.mem_sup_right (hAmem f₂ χ₂ hA₂ y hy)
    exact fun y hy => hle hy
  refine ⟨map_normalized θ σ α A κ hαθ hA hA2 _ hSA, ?_⟩
  constructor
  · intro hfix
    obtain ⟨w₀, hw₀⟩ := exists_ne (0 : W)
    have hxS : f₁ (Multiplicative.ofAdd w₀) ∈ f₁.range ⊔ f₂.range :=
      Subgroup.mem_sup_left ⟨_, rfl⟩
    have h1 := hfix (θ (κ * f₁ (Multiplicative.ofAdd w₀) * κ⁻¹))
      ⟨κ * f₁ (Multiplicative.ofAdd w₀) * κ⁻¹, ⟨_, hxS, rfl⟩, rfl⟩
    rw [← hαθ, hA, hA₁] at h1
    have h2 : κ * f₁ (Multiplicative.ofAdd ((χ₁ - 1) • w₀)) * κ⁻¹ ∈ Subgroup.center K := by
      apply hker
      rw [MonoidHom.mem_ker]
      have e : f₁ (Multiplicative.ofAdd ((χ₁ - 1) • w₀)) =
          (f₁ (Multiplicative.ofAdd w₀))⁻¹ * f₁ (Multiplicative.ofAdd (χ₁ • w₀)) := by
        rw [← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add]
        congr 2
        module
      have e2 : κ * f₁ (Multiplicative.ofAdd ((χ₁ - 1) • w₀)) * κ⁻¹ =
          (κ * f₁ (Multiplicative.ofAdd w₀) * κ⁻¹)⁻¹ *
            (κ * f₁ (Multiplicative.ofAdd (χ₁ • w₀)) * κ⁻¹) := by
        rw [e]
        group
      rw [e2, map_mul, map_inv, ← h1, inv_mul_cancel]
    have hc : f₁ (Multiplicative.ofAdd ((χ₁ - 1) • w₀)) ∈ Subgroup.center K := by
      have h3 := Subgroup.Normal.conj_mem
        (inferInstance : (Subgroup.center K).Normal) _ h2 κ⁻¹
      have h4 : κ⁻¹ * (κ * f₁ (Multiplicative.ofAdd ((χ₁ - 1) • w₀)) * κ⁻¹) * κ⁻¹⁻¹ =
          f₁ (Multiplicative.ofAdd ((χ₁ - 1) • w₀)) := by group
      rwa [h4] at h3
    have h5 := hZ _ hc (hp₁ ((χ₁ - 1) • w₀))
    have h6 : f₁ (Multiplicative.ofAdd ((χ₁ - 1) • w₀)) = f₁ (Multiplicative.ofAdd 0) := by
      rw [ofAdd_zero, map_one]
      exact h5
    have h7 := Multiplicative.ofAdd.injective (hf₁ h6)
    exact sub_eq_zero.mp ((smul_eq_zero.mp h7).resolve_right hw₀)
  · intro hχ1
    have hχ2 := hχ hχ1
    have hle : f₁.range ⊔ f₂.range ≤ MonoidHom.eqLocus A.toMonoidHom (MonoidHom.id _) := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · obtain ⟨c, rfl⟩ := hy
        rw [← ofAdd_toAdd c]
        change A _ = _
        rw [hA₁, hχ1, one_smul]
        rfl
      · obtain ⟨c, rfl⟩ := hy
        rw [← ofAdd_toAdd c]
        change A _ = _
        rw [hA₂, hχ2, one_smul]
        rfl
    exact fixed_of_fixed θ σ α A κ hαθ hA _ (fun y hy => hle hy)


section Maps

variable {K X : Type*} [Group K] [Group X] {p : ℕ} {W : Type} [AddCommGroup W]

theorem map_sq_of_involution (A : K ≃* K) (hA2 : ∀ y, A (A y) = y) (f : Multiplicative W →* K)
    (hf : Function.Injective f) (M : W → W)
    (hA : ∀ c : W, A (f (Multiplicative.ofAdd c)) = f (Multiplicative.ofAdd (M c))) (c : W) :
    M (M c) = c := by
  have h1 := hA2 (f (Multiplicative.ofAdd c))
  rw [hA, hA] at h1
  exact Multiplicative.ofAdd.injective (hf h1)

theorem normalizes_and_fixes_of_map
    (hZ : ∀ ζ ∈ Subgroup.center K, ζ ^ p = 1 → ζ = 1) (θ : K →* X)
    (hker : θ.ker ≤ Subgroup.center K) (σ : X ≃* X) (α A : K ≃* K) (κ : K)
    (hαθ : ∀ y, θ (α y) = σ (θ y)) (hA : ∀ y, α (κ * y * κ⁻¹) = κ * A y * κ⁻¹)
    (hA2 : ∀ y, A (A y) = y) (f₁ f₂ : Multiplicative W →* K) (hf₁ : Function.Injective f₁)
    (hp₁ : ∀ c : W, (f₁ (Multiplicative.ofAdd c)) ^ p = 1) (M₁ M₂ : W → W)
    (hA₁ : ∀ c : W, A (f₁ (Multiplicative.ofAdd c)) = f₁ (Multiplicative.ofAdd (M₁ c)))
    (hA₂ : ∀ c : W, A (f₂ (Multiplicative.ofAdd c)) = f₂ (Multiplicative.ofAdd (M₂ c)))
    (hM : (∀ w, M₁ w = w) → ∀ w, M₂ w = w) :
    ((((f₁.range ⊔ f₂.range).map (MulAut.conj κ).toMonoidHom).map θ).map σ.toMonoidHom =
      ((f₁.range ⊔ f₂.range).map (MulAut.conj κ).toMonoidHom).map θ) ∧
    ((∀ y ∈ ((f₁.range ⊔ f₂.range).map (MulAut.conj κ).toMonoidHom).map θ, σ y = y) ↔
      ∀ w, M₁ w = w) := by
  have hAmem : ∀ (f : Multiplicative W →* K) (M : W → W),
      (∀ c : W, A (f (Multiplicative.ofAdd c)) = f (Multiplicative.ofAdd (M c))) →
        ∀ y ∈ f.range, A y ∈ f.range := by
    intro f M hf
    rintro y ⟨c, rfl⟩
    rw [← ofAdd_toAdd c, hf]
    exact ⟨_, rfl⟩
  have hSA : ∀ y ∈ f₁.range ⊔ f₂.range, A y ∈ f₁.range ⊔ f₂.range := by
    have hle : f₁.range ⊔ f₂.range ≤ (f₁.range ⊔ f₂.range).comap A.toMonoidHom := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · exact Subgroup.mem_sup_left (hAmem f₁ M₁ hA₁ y hy)
      · exact Subgroup.mem_sup_right (hAmem f₂ M₂ hA₂ y hy)
    exact fun y hy => hle hy
  refine ⟨map_normalized θ σ α A κ hαθ hA hA2 _ hSA, ?_⟩
  constructor
  · intro hfix w
    have hxS : f₁ (Multiplicative.ofAdd w) ∈ f₁.range ⊔ f₂.range :=
      Subgroup.mem_sup_left ⟨_, rfl⟩
    have h1 := hfix (θ (κ * f₁ (Multiplicative.ofAdd w) * κ⁻¹))
      ⟨κ * f₁ (Multiplicative.ofAdd w) * κ⁻¹, ⟨_, hxS, rfl⟩, rfl⟩
    rw [← hαθ, hA, hA₁] at h1
    have h2 : κ * f₁ (Multiplicative.ofAdd (M₁ w - w)) * κ⁻¹ ∈ Subgroup.center K := by
      apply hker
      rw [MonoidHom.mem_ker]
      have e : f₁ (Multiplicative.ofAdd (M₁ w - w)) =
          (f₁ (Multiplicative.ofAdd w))⁻¹ * f₁ (Multiplicative.ofAdd (M₁ w)) := by
        rw [← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add]
        congr 2
        abel
      have e2 : κ * f₁ (Multiplicative.ofAdd (M₁ w - w)) * κ⁻¹ =
          (κ * f₁ (Multiplicative.ofAdd w) * κ⁻¹)⁻¹ *
            (κ * f₁ (Multiplicative.ofAdd (M₁ w)) * κ⁻¹) := by
        rw [e]
        group
      rw [e2, map_mul, map_inv, ← h1, inv_mul_cancel]
    have hc : f₁ (Multiplicative.ofAdd (M₁ w - w)) ∈ Subgroup.center K := by
      have h3 := Subgroup.Normal.conj_mem
        (inferInstance : (Subgroup.center K).Normal) _ h2 κ⁻¹
      have h4 : κ⁻¹ * (κ * f₁ (Multiplicative.ofAdd (M₁ w - w)) * κ⁻¹) * κ⁻¹⁻¹ =
          f₁ (Multiplicative.ofAdd (M₁ w - w)) := by group
      rwa [h4] at h3
    have h5 := hZ _ hc (hp₁ (M₁ w - w))
    have h6 : f₁ (Multiplicative.ofAdd (M₁ w - w)) = f₁ (Multiplicative.ofAdd 0) := by
      rw [ofAdd_zero, map_one]
      exact h5
    exact sub_eq_zero.mp (Multiplicative.ofAdd.injective (hf₁ h6))
  · intro hM1
    have hM2 := hM hM1
    have hle : f₁.range ⊔ f₂.range ≤ MonoidHom.eqLocus A.toMonoidHom (MonoidHom.id _) := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · obtain ⟨c, rfl⟩ := hy
        rw [← ofAdd_toAdd c]
        change A _ = _
        rw [hA₁, hM1]
        rfl
      · obtain ⟨c, rfl⟩ := hy
        rw [← ofAdd_toAdd c]
        change A _ = _
        rw [hA₂, hM2]
        rfl
    exact fixed_of_fixed θ σ α A κ hαθ hA _ (fun y hy => hle hy)

end Maps

end CFSG.ClassicalInvolution.ModelFacts.OrthAut
