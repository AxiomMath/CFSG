module

public import CFSG.ClassicalGroups.Symplectic.InvariantForm

public section

namespace CFSG.ClassicalGroups.Symplectic

open CFSG.Open Matrix
open LinearMap (BilinForm)

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_smul_of_intertwiners (hm : 1 ≤ m) {H : Type*} [Group H]
    (ρ : H →* GL (Fin m ⊕ Fin m) K) (hρ : ρ.range = StatedSp m K) (σ : H → H)
    (p p' : (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K))
    (hp : ∀ (s : H) (x : Fin m ⊕ Fin m → K),
      p ((ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) =
        (ρ (σ s) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ p x)
    (hp' : ∀ (s : H) (x : Fin m ⊕ Fin m → K),
      p' ((ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) =
        (ρ (σ s) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ p' x)
    (hp0 : p ≠ 0) :
    ∃ (μ : K) (s₀ : GL (Fin m ⊕ Fin m) K) (c : K), μ ≠ 0 ∧ s₀ ∈ StatedSp m K ∧
      (∀ x, p x = μ • ((s₀ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) ∧
        ∀ x, p' x = c • p x := by
  classical
  have hinv : ∀ A ∈ StatedSp m K, ∀ w ∈ LinearMap.ker p,
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ w ∈ LinearMap.ker p := by
    intro A hA w hw
    rw [← hρ] at hA
    obtain ⟨s, rfl⟩ := hA
    rw [LinearMap.mem_ker] at hw ⊢
    rw [hp s w, hw, Matrix.mulVec_zero]
  have hker : LinearMap.ker p = ⊥ := by
    rcases eq_bot_or_eq_top_of_invariant_statedSp (LinearMap.ker p) hinv with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.mp h) hp0
  have hinj : Function.Injective p := LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective p := LinearMap.injective_iff_surjective.mp hinj
  let M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K := LinearMap.toMatrix' p
  have hM : ∀ x, M *ᵥ x = p x := fun x => by
    rw [LinearMap.toMatrix'_mulVec]
  have hMu : IsUnit M := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro x y hxy
    exact hinj (by rw [← hM, ← hM]; exact hxy)
  let γ : GL (Fin m ⊕ Fin m) K := hMu.unit
  have hγ : (γ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = M := rfl
  have hγp : ∀ x, (γ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x = p x := fun x => by
    rw [hγ, hM]
  have hconj : ∀ s : H, γ * ρ s * γ⁻¹ = ρ (σ s) := by
    intro s
    apply Units.ext
    show (γ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
      (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
      ((γ⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = _
    have h1 : (γ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
        (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
        (ρ (σ s) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
          (γ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := by
      ext i j
      have := hp s (Pi.single j 1)
      rw [← hγp, ← hγp, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
      have := congrFun this i
      simpa [Matrix.mulVec_single_one] using this
    rw [h1, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have hnorm : ∀ A ∈ StatedSp m K, γ * A * γ⁻¹ ∈ StatedSp m K := by
    intro A hA
    rw [← hρ] at hA
    obtain ⟨s, rfl⟩ := hA
    rw [hconj s, ← hρ]
    exact ⟨σ s, rfl⟩
  obtain ⟨μ, s₀, hμ, hs₀, hγs⟩ := exists_smul_statedSp_of_normalizes hm hnorm
  let N : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
    ((γ⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
  let f : (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K) := (Matrix.mulVecLin N) ∘ₗ p'
  have hfcomm : ∀ A ∈ StatedSp m K, ∀ x : Fin m ⊕ Fin m → K,
      f ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) =
        (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ f x := by
    intro A hA x
    rw [← hρ] at hA
    obtain ⟨s, rfl⟩ := hA
    have h1 : γ⁻¹ * ρ (σ s) = ρ s * γ⁻¹ := by rw [← hconj s]; group
    have h2 : N * (ρ (σ s) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
        (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * N := by
      have := congrArg (fun u : GL (Fin m ⊕ Fin m) K =>
        (u : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) h1
      simpa [N] using this
    show N *ᵥ p' ((ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) =
      (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ (N *ᵥ p' x)
    rw [hp' s x, Matrix.mulVec_mulVec, h2, Matrix.mulVec_mulVec]
  obtain ⟨c, hc⟩ := exists_eq_smul_of_commute_statedSp hm f hfcomm
  refine ⟨μ, s₀, c, hμ, hs₀, fun x => by rw [← hγp, hγs], fun x => ?_⟩
  have h3 : N *ᵥ p' x = c • x := hc x
  have h4 : p' x = (γ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ (N *ᵥ p' x) := by
    rw [Matrix.mulVec_mulVec]
    have h5 : (γ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * N = 1 := by
      show (γ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
        ((γ⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = 1
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [h5, Matrix.one_mulVec]
  rw [h4, h3, Matrix.mulVec_smul, hγp]

theorem exists_smul_eq_of_intertwiners (hm : 1 ≤ m) {H : Type*} [Group H]
    (ρ : H →* GL (Fin m ⊕ Fin m) K) (hρ : ρ.range = StatedSp m K) (σ : H → H)
    (p p' : (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K))
    (hp : ∀ (s : H) (x : Fin m ⊕ Fin m → K),
      p ((ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) =
        (ρ (σ s) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ p x)
    (hp' : ∀ (s : H) (x : Fin m ⊕ Fin m → K),
      p' ((ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) =
        (ρ (σ s) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ p' x)
    (hp0 : p ≠ 0) : ∃ c : K, ∀ x, p' x = c • p x := by
  obtain ⟨-, -, c, -, -, -, hc⟩ := exists_smul_of_intertwiners hm ρ hρ σ p p' hp hp' hp0
  exact ⟨c, hc⟩

theorem exists_smul_statedSp_of_intertwiner (hm : 1 ≤ m) {H : Type*} [Group H]
    (ρ : H →* GL (Fin m ⊕ Fin m) K) (hρ : ρ.range = StatedSp m K) (σ : H → H)
    (p : (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K))
    (hp : ∀ (s : H) (x : Fin m ⊕ Fin m → K),
      p ((ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) =
        (ρ (σ s) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ p x)
    (hp0 : p ≠ 0) :
    ∃ (μ : K) (s₀ : GL (Fin m ⊕ Fin m) K), μ ≠ 0 ∧ s₀ ∈ StatedSp m K ∧
      ∀ x, p x = μ • ((s₀ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) := by
  obtain ⟨μ, s₀, -, hμ, hs₀, hps, -⟩ := exists_smul_of_intertwiners hm ρ hρ σ p p hp hp hp0
  exact ⟨μ, s₀, hμ, hs₀, hps⟩

theorem exists_tensor_of_normalizes (hm : 1 ≤ m) {E : Type*} [AddCommGroup E] [Module K E]
    {W₁ W₂ : Submodule K E} (hdisj : W₁ ⊓ W₂ = ⊥)
    (e₁ : W₁ ≃ₗ[K] (Fin m ⊕ Fin m → K)) (e₂ : W₂ ≃ₗ[K] (Fin m ⊕ Fin m → K))
    {H : Type*} [Group H] (Φ : H →* (E ≃ₗ[K] E)) (ρ : H →* GL (Fin m ⊕ Fin m) K)
    (hρ : ρ.range = StatedSp m K)
    (hW₁ : ∀ s : H, ∀ w ∈ W₁, Φ s w ∈ W₁) (hW₂ : ∀ s : H, ∀ w ∈ W₂, Φ s w ∈ W₂)
    (he₁ : ∀ (s : H) (w : W₁),
      e₁ ⟨Φ s w, hW₁ s w w.2⟩ = (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ e₁ w)
    (he₂ : ∀ (s : H) (w : W₂),
      e₂ ⟨Φ s w, hW₂ s w w.2⟩ = (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ e₂ w)
    (T : E ≃ₗ[K] E) (hT : ∀ y ∈ W₁ ⊔ W₂, T y ∈ W₁ ⊔ W₂) (σ : H → H)
    (hσ : ∀ (s : H) (y : E), T (Φ s y) = Φ (σ s) (T y)) :
    ∃ (s₀ : GL (Fin m ⊕ Fin m) K) (h₁₁ h₁₂ h₂₁ h₂₂ : K), s₀ ∈ StatedSp m K ∧
      ∀ x : Fin m ⊕ Fin m → K,
        T ((e₁.symm x : W₁) : E) =
          ((e₁.symm (h₁₁ • ((s₀ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₁) : E) +
          ((e₂.symm (h₂₁ • ((s₀ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₂) : E) ∧
        T ((e₂.symm x : W₂) : E) =
          ((e₁.symm (h₁₂ • ((s₀ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₁) : E) +
          ((e₂.symm (h₂₂ • ((s₀ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₂) : E) := by
  classical
  let N := Fin m ⊕ Fin m → K
  let Θ : (N × N) →ₗ[K] E :=
    (W₁.subtype ∘ₗ e₁.symm.toLinearMap) ∘ₗ LinearMap.fst K N N +
      (W₂.subtype ∘ₗ e₂.symm.toLinearMap) ∘ₗ LinearMap.snd K N N
  have hΘ : ∀ x x' : N, Θ (x, x') = ((e₁.symm x : W₁) : E) + ((e₂.symm x' : W₂) : E) :=
    fun x x' => rfl
  have hΘinj : Function.Injective Θ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, x'⟩ hx
    rw [LinearMap.mem_ker, hΘ] at hx
    have h1 : ((e₁.symm x : W₁) : E) = -((e₂.symm x' : W₂) : E) := eq_neg_of_add_eq_zero_left hx
    have hmem : ((e₁.symm x : W₁) : E) ∈ W₁ ⊓ W₂ :=
      ⟨(e₁.symm x).2, h1 ▸ W₂.neg_mem (e₂.symm x').2⟩
    rw [hdisj, Submodule.mem_bot] at hmem
    have hx0 : x = 0 := by
      have : e₁.symm x = 0 := Subtype.ext hmem
      simpa using this
    have hx'0 : x' = 0 := by
      rw [hmem] at h1
      have : e₂.symm x' = 0 := Subtype.ext (neg_eq_zero.mp h1.symm)
      simpa using this
    simp [hx0, hx'0]
  have hΘrange : ∀ y, y ∈ W₁ ⊔ W₂ → ∃ v, Θ v = y := by
    intro y hy
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp hy
    exact ⟨(e₁ ⟨w₁, hw₁⟩, e₂ ⟨w₂, hw₂⟩), by rw [hΘ]; simp⟩
  have hΘmem : ∀ v, Θ v ∈ W₁ ⊔ W₂ := fun v =>
    Submodule.add_mem_sup (e₁.symm v.1).2 (e₂.symm v.2).2
  have hPex : ∀ v, ∃ v', Θ v' = T (Θ v) := fun v => hΘrange _ (hT _ (hΘmem v))
  choose P hP using hPex
  have hPadd : ∀ v w, P (v + w) = P v + P w := fun v w => by
    apply hΘinj
    rw [hP, map_add, map_add, map_add, hP, hP]
  have hPsmul : ∀ (c : K) v, P (c • v) = c • P v := fun c v => by
    apply hΘinj
    rw [hP, map_smul, map_smul, map_smul, hP]
  let Pl : (N × N) →ₗ[K] (N × N) := { toFun := P, map_add' := hPadd, map_smul' := hPsmul }
  have hPl : ∀ v, Θ (Pl v) = T (Θ v) := hP
  have hΦ₁ : ∀ (s : H) (x : N), Φ s ((e₁.symm x : W₁) : E) = ((e₁.symm
      ((ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) : W₁) : E) := by
    intro s x
    have h1 := he₁ s (e₁.symm x)
    rw [LinearEquiv.apply_symm_apply] at h1
    have h2 : (⟨Φ s (e₁.symm x : W₁), hW₁ s _ (e₁.symm x).2⟩ : W₁) =
        e₁.symm ((ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) := by
      apply e₁.injective
      rw [h1, LinearEquiv.apply_symm_apply]
    exact congrArg Subtype.val h2
  have hΦ₂ : ∀ (s : H) (x : N), Φ s ((e₂.symm x : W₂) : E) = ((e₂.symm
      ((ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) : W₂) : E) := by
    intro s x
    have h1 := he₂ s (e₂.symm x)
    rw [LinearEquiv.apply_symm_apply] at h1
    have h2 : (⟨Φ s (e₂.symm x : W₂), hW₂ s _ (e₂.symm x).2⟩ : W₂) =
        e₂.symm ((ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) := by
      apply e₂.injective
      rw [h1, LinearEquiv.apply_symm_apply]
    exact congrArg Subtype.val h2
  have hΦΘ : ∀ (s : H) (v : N × N), Φ s (Θ v) =
      Θ ((ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v.1,
        (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v.2) := by
    intro s v
    obtain ⟨x, x'⟩ := v
    rw [hΘ, hΘ, map_add, hΦ₁, hΦ₂]
  have hPint : ∀ (s : H) (v : N × N), Pl ((ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v.1,
      (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v.2) =
      ((ρ (σ s) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ (Pl v).1,
        (ρ (σ s) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ (Pl v).2) := by
    intro s v
    apply hΘinj
    have e1 : Θ (Pl ((ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v.1,
        (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v.2)) = Φ (σ s) (T (Θ v)) := by
      rw [hPl, ← hΦΘ s v, hσ]
    have e2 : Θ ((ρ (σ s) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ (Pl v).1,
        (ρ (σ s) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ (Pl v).2) =
          Φ (σ s) (T (Θ v)) := by
      rw [← hΦΘ (σ s) (Pl v), hPl]
    rw [e1, e2]
  let p₁₁ : N →ₗ[K] N := LinearMap.fst K N N ∘ₗ Pl ∘ₗ LinearMap.inl K N N
  let p₂₁ : N →ₗ[K] N := LinearMap.snd K N N ∘ₗ Pl ∘ₗ LinearMap.inl K N N
  let p₁₂ : N →ₗ[K] N := LinearMap.fst K N N ∘ₗ Pl ∘ₗ LinearMap.inr K N N
  let p₂₂ : N →ₗ[K] N := LinearMap.snd K N N ∘ₗ Pl ∘ₗ LinearMap.inr K N N
  have hint₁ : ∀ (s : H) (x : N),
      (Pl ((ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x, 0)) =
        ((ρ (σ s) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ (Pl (x, 0)).1,
          (ρ (σ s) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ (Pl (x, 0)).2) := by
    intro s x
    have := hPint s (x, 0)
    simpa [Matrix.mulVec_zero] using this
  have hint₂ : ∀ (s : H) (x : N),
      (Pl (0, (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) =
        ((ρ (σ s) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ (Pl (0, x)).1,
          (ρ (σ s) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ (Pl (0, x)).2) := by
    intro s x
    have := hPint s (0, x)
    simpa [Matrix.mulVec_zero] using this
  have h11 : ∀ (s : H) (x : N), p₁₁ ((ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) =
      (ρ (σ s) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ p₁₁ x := fun s x =>
    congrArg Prod.fst (hint₁ s x)
  have h21 : ∀ (s : H) (x : N), p₂₁ ((ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) =
      (ρ (σ s) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ p₂₁ x := fun s x =>
    congrArg Prod.snd (hint₁ s x)
  have h12 : ∀ (s : H) (x : N), p₁₂ ((ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) =
      (ρ (σ s) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ p₁₂ x := fun s x =>
    congrArg Prod.fst (hint₂ s x)
  have h22 : ∀ (s : H) (x : N), p₂₂ ((ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) =
      (ρ (σ s) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ p₂₂ x := fun s x =>
    congrArg Prod.snd (hint₂ s x)
  have hT₁ : ∀ x : N, T ((e₁.symm x : W₁) : E) =
      ((e₁.symm (p₁₁ x) : W₁) : E) + ((e₂.symm (p₂₁ x) : W₂) : E) := by
    intro x
    have h0 : Θ (x, 0) = ((e₁.symm x : W₁) : E) := by rw [hΘ]; simp
    rw [← h0, ← hPl, ← hΘ]
    rfl
  have hT₂ : ∀ x : N, T ((e₂.symm x : W₂) : E) =
      ((e₁.symm (p₁₂ x) : W₁) : E) + ((e₂.symm (p₂₂ x) : W₂) : E) := by
    intro x
    have h0 : Θ (0, x) = ((e₂.symm x : W₂) : E) := by rw [hΘ]; simp
    rw [← h0, ← hPl, ← hΘ]
    rfl
  have hex : p₁₁ ≠ 0 ∨ p₂₁ ≠ 0 ∨ p₁₂ ≠ 0 ∨ p₂₂ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨c11, c21, c12, c22⟩ := hcon
    let i0 : Fin m := ⟨0, hm⟩
    let x₀ : Fin m ⊕ Fin m → K := Pi.single (Sum.inl i0) 1
    have hx₀ : x₀ ≠ 0 := by
      intro h
      have h' : (Pi.single (Sum.inl i0) 1 : Fin m ⊕ Fin m → K) = 0 := h
      have := congrFun h' (Sum.inl i0)
      simp at this
    have h1 : T ((e₁.symm x₀ : W₁) : E) = 0 := by
      rw [hT₁, c11, c21]
      simp
    have h2 : ((e₁.symm x₀ : W₁) : E) = 0 := by
      have := T.injective (h1.trans (map_zero T).symm)
      exact this
    exact hx₀ (by
      have : e₁.symm x₀ = 0 := Subtype.ext h2
      simpa using this)
  have key : ∀ q : N →ₗ[K] N, q ≠ 0 →
      (∀ (s : H) (x : N), q ((ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) =
        (ρ (σ s) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ q x) →
      ∃ (s₀ : GL (Fin m ⊕ Fin m) K) (h₁₁ h₁₂ h₂₁ h₂₂ : K), s₀ ∈ StatedSp m K ∧ ∀ x : N,
        p₁₁ x = h₁₁ • ((s₀ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) ∧
        p₁₂ x = h₁₂ • ((s₀ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) ∧
        p₂₁ x = h₂₁ • ((s₀ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) ∧
        p₂₂ x = h₂₂ • ((s₀ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) := by
    intro q hq0 hq
    obtain ⟨μ, s₀, hμ, hs₀, hqs⟩ := exists_smul_statedSp_of_intertwiner hm ρ hρ σ q hq hq0
    obtain ⟨c11, hc11⟩ := exists_smul_eq_of_intertwiners hm ρ hρ σ q p₁₁ hq h11 hq0
    obtain ⟨c12, hc12⟩ := exists_smul_eq_of_intertwiners hm ρ hρ σ q p₁₂ hq h12 hq0
    obtain ⟨c21, hc21⟩ := exists_smul_eq_of_intertwiners hm ρ hρ σ q p₂₁ hq h21 hq0
    obtain ⟨c22, hc22⟩ := exists_smul_eq_of_intertwiners hm ρ hρ σ q p₂₂ hq h22 hq0
    refine ⟨s₀, c11 * μ, c12 * μ, c21 * μ, c22 * μ, hs₀, fun x => ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [hc11, hqs, smul_smul]
    · rw [hc12, hqs, smul_smul]
    · rw [hc21, hqs, smul_smul]
    · rw [hc22, hqs, smul_smul]
  obtain ⟨s₀, h₁₁, h₁₂, h₂₁, h₂₂, hs₀, hblk⟩ : ∃ (s₀ : GL (Fin m ⊕ Fin m) K)
      (h₁₁ h₁₂ h₂₁ h₂₂ : K), s₀ ∈ StatedSp m K ∧ ∀ x : N,
        p₁₁ x = h₁₁ • ((s₀ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) ∧
        p₁₂ x = h₁₂ • ((s₀ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) ∧
        p₂₁ x = h₂₁ • ((s₀ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) ∧
        p₂₂ x = h₂₂ • ((s₀ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) := by
    rcases hex with h | h | h | h
    · exact key p₁₁ h h11
    · exact key p₂₁ h h21
    · exact key p₁₂ h h12
    · exact key p₂₂ h h22
  refine ⟨s₀, h₁₁, h₁₂, h₂₁, h₂₂, hs₀, fun x => ⟨?_, ?_⟩⟩
  · rw [hT₁, (hblk x).1, (hblk x).2.2.1]
  · rw [hT₂, (hblk x).2.1, (hblk x).2.2.2]

end CFSG.ClassicalGroups.Symplectic
