module

public import CFSG.CGT.T75F.E710Num3

public section

namespace CFSG.CGT.T75F

theorem le_of_invariant_complement {X : Type*} [Group X] [Finite X] {M L₁ L₂ : Subgroup X}
    (hMc : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a) (hMsq : ∀ a ∈ M, a * a = 1) {s : X}
    (hs : ∀ m ∈ M, s * m * s⁻¹ ∈ M)
    (hfix : ∀ m ∈ M, s * m * s⁻¹ = m → m ∈ Subgroup.center X)
    (hL₁M : L₁ ≤ M) (hL₂M : L₂ ≤ M)
    (hL₁inv : ∀ l ∈ L₁, s * l * s⁻¹ ∈ L₁) (hL₂inv : ∀ l ∈ L₂, s * l * s⁻¹ ∈ L₂)
    (hL₁c : ∀ x ∈ L₁, x ∈ Subgroup.center X → x = 1)
    (hL₂c : ∀ x ∈ M, ∃ y ∈ L₂, y⁻¹ * x ∈ Subgroup.center X) : L₁ ≤ L₂ := by
  have hg_mem : ∀ x ∈ L₁, s * x * s⁻¹ * x ∈ L₁ ⊓ L₂ := by
    intro x hx
    refine ⟨L₁.mul_mem (hL₁inv x hx) hx, ?_⟩
    obtain ⟨y, hy, hc⟩ := hL₂c x (hL₁M hx)
    obtain ⟨c, hcdef⟩ : ∃ c : X, c = y⁻¹ * x := ⟨_, rfl⟩
    rw [← hcdef] at hc
    have hcM : c ∈ M := by
      rw [hcdef]
      exact M.mul_mem (M.inv_mem (hL₂M hy)) (hL₁M hx)
    have hxyc : x = y * c := by rw [hcdef]; group
    have hccomm : ∀ z : X, z * c = c * z := Subgroup.mem_center_iff.1 hc
    have hcs : s * c * s⁻¹ = c := by
      calc s * c * s⁻¹ = c * s * s⁻¹ := by rw [hccomm s]
        _ = c := by group
    have hcc : c * c = 1 := hMsq c hcM
    have hxeq : s * x * s⁻¹ * x = s * y * s⁻¹ * y := by
      calc s * x * s⁻¹ * x = (s * y * s⁻¹) * (s * c * s⁻¹) * y * c := by rw [hxyc]; group
        _ = (s * y * s⁻¹) * c * y * c := by rw [hcs]
        _ = (s * y * s⁻¹) * (c * y) * c := by group
        _ = (s * y * s⁻¹) * (y * c) * c := by rw [← hccomm y]
        _ = (s * y * s⁻¹) * y * (c * c) := by group
        _ = (s * y * s⁻¹) * y := by rw [hcc, mul_one]
    rw [hxeq]
    exact L₂.mul_mem (hL₂inv y hy) hy
  have hinj : Function.Injective
      (fun x : L₁ => (⟨s * x * s⁻¹ * x, hg_mem x x.2⟩ : ↥(L₁ ⊓ L₂))) := by
    intro x x' hxx'
    have hg : s * x * s⁻¹ * x = s * x' * s⁻¹ * x' := congrArg Subtype.val hxx'
    have hxM : (x : X) ∈ M := hL₁M x.2
    have hx'M : (x' : X) ∈ M := hL₁M x'.2
    have hAM : s * x * s⁻¹ ∈ M := hs _ hxM
    have hA'M : s * x' * s⁻¹ ∈ M := hs _ hx'M
    have hcomm := hMc (s * x' * s⁻¹) hA'M x hxM
    have h1 : (s * x * s⁻¹ * (s * x' * s⁻¹)) * (x * x') =
        (s * x * s⁻¹ * x) * (s * x' * s⁻¹ * x') := by
      calc (s * x * s⁻¹ * (s * x' * s⁻¹)) * (x * x')
          = (s * x * s⁻¹) * ((s * x' * s⁻¹) * x) * x' := by group
        _ = (s * x * s⁻¹) * (x * (s * x' * s⁻¹)) * x' := by rw [hcomm]
        _ = (s * x * s⁻¹ * x) * (s * x' * s⁻¹ * x') := by group
    have hgx : (s * x * s⁻¹ * x) * (s * x' * s⁻¹ * x') = 1 := by
      rw [← hg]
      exact hMsq _ (M.mul_mem hAM hxM)
    have h2 : s * (x * x') * s⁻¹ * (x * x') = 1 := by
      calc s * (x * x') * s⁻¹ * (x * x')
          = (s * x * s⁻¹ * (s * x' * s⁻¹)) * (x * x') := by group
        _ = 1 := by rw [h1, hgx]
    have hxx'M : (x : X) * x' ∈ M := M.mul_mem hxM hx'M
    have hfixed : s * (x * x') * s⁻¹ = x * x' := by
      have h3 : s * (x * x') * s⁻¹ = (x * x')⁻¹ := eq_inv_of_mul_eq_one_left h2
      rw [h3]
      exact inv_eq_of_mul_eq_one_right (hMsq _ hxx'M)
    have hcen := hfix _ hxx'M hfixed
    have h4 : (x : X) * x' = 1 := hL₁c _ (L₁.mul_mem x.2 x'.2) hcen
    apply Subtype.ext
    have h5 : (x' : X) = (x : X)⁻¹ := eq_inv_of_mul_eq_one_right h4
    rw [h5]
    exact (inv_eq_of_mul_eq_one_right (hMsq _ hxM)).symm
  have hcard := Nat.card_le_card_of_injective _ hinj
  have heq : L₁ ⊓ L₂ = L₁ := Subgroup.eq_of_le_of_card_ge inf_le_left hcard
  intro x hx
  rw [← heq] at hx
  exact hx.2

variable {X : Type} [Group X] [Finite X] {D : Set X} {M L : Subgroup X} {q : ℕ}
  {q' : ℕ} {δ : X ⧸ Subgroup.center X}

namespace Torus710

omit [Finite X] in
theorem fix_all (hT : Torus710 M q' δ) (i : ℕ) {ω₀ : X ⧸ Subgroup.center X} (hω₀ : ω₀ ∈ Mhat M)
    (hω₀1 : ω₀ ≠ 1) (hfix : δ ^ i * ω₀ * (δ ^ i)⁻¹ = ω₀) :
    ∀ ω ∈ Mhat M, δ ^ i * ω * (δ ^ i)⁻¹ = ω := by
  intro ω hω
  by_cases hω1 : ω = 1
  · rw [hω1]; group
  obtain ⟨j, hj⟩ := hT.trans ω₀ hω₀ hω₀1 ω hω hω1
  have hcomm : δ ^ i * δ ^ j = δ ^ j * δ ^ i := by rw [← pow_add, ← pow_add, add_comm]
  rw [← hj]
  calc δ ^ i * (δ ^ j * ω₀ * (δ ^ j)⁻¹) * (δ ^ i)⁻¹
      = (δ ^ i * δ ^ j) * ω₀ * (δ ^ i * δ ^ j)⁻¹ := by group
    _ = (δ ^ j * δ ^ i) * ω₀ * (δ ^ j * δ ^ i)⁻¹ := by rw [hcomm]
    _ = δ ^ j * (δ ^ i * ω₀ * (δ ^ i)⁻¹) * (δ ^ j)⁻¹ := by group
    _ = δ ^ j * ω₀ * (δ ^ j)⁻¹ := by rw [hfix]

omit [Finite X] in
theorem card_le_of_central (hT : Torus710 M q' δ) {μ : ℕ} (hμ : 0 < μ)
    {ω₀ : X ⧸ Subgroup.center X} (hω₀ : ω₀ ∈ Mhat M) (hω₀1 : ω₀ ≠ 1)
    (hcen : ∀ ω ∈ Mhat M, δ ^ μ * ω * (δ ^ μ)⁻¹ = ω) : q' - 1 ≤ μ := by
  have hpow : ∀ k : ℕ, ∀ ω ∈ Mhat M, δ ^ (μ * k) * ω * (δ ^ (μ * k))⁻¹ = ω := by
    intro k
    induction k with
    | zero => intro ω _; simp
    | succ k ih =>
      intro ω hω
      calc δ ^ (μ * (k + 1)) * ω * (δ ^ (μ * (k + 1)))⁻¹
          = δ ^ (μ * k) * (δ ^ μ * ω * (δ ^ μ)⁻¹) * (δ ^ (μ * k))⁻¹ := by
            rw [mul_add, mul_one, pow_add]; group
        _ = ω := by rw [hcen ω hω]; exact ih ω hω
  have hsub : (((Mhat M : Subgroup (X ⧸ Subgroup.center X)) : Set (X ⧸ Subgroup.center X)) \
      ({1} : Set (X ⧸ Subgroup.center X))) ⊆
      (fun r : ℕ => δ ^ r * ω₀ * (δ ^ r)⁻¹) '' (Set.Iio μ) := by
    rintro ω ⟨hω, hω1⟩
    have hω1' : ω ≠ 1 := fun h' => hω1 (by simpa using h')
    obtain ⟨j, hj⟩ := hT.trans ω₀ hω₀ hω₀1 ω hω hω1'
    refine ⟨j % μ, Nat.mod_lt _ hμ, ?_⟩
    have hjeq : δ ^ j = δ ^ (μ * (j / μ)) * δ ^ (j % μ) := by
      rw [← pow_add, Nat.div_add_mod]
    have hin := hT.normalizes (j % μ) ω₀ hω₀
    show δ ^ (j % μ) * ω₀ * (δ ^ (j % μ))⁻¹ = ω
    rw [← hj, hjeq]
    have := hpow (j / μ) _ hin
    calc δ ^ (j % μ) * ω₀ * (δ ^ (j % μ))⁻¹
        = δ ^ (μ * (j / μ)) * (δ ^ (j % μ) * ω₀ * (δ ^ (j % μ))⁻¹) * (δ ^ (μ * (j / μ)))⁻¹ :=
          this.symm
      _ = _ := by group
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ((fun r : ℕ => δ ^ r * ω₀ * (δ ^ r)⁻¹) '' (Set.Iio μ)).ncard ≤ (Set.Iio μ).ncard :=
    Set.ncard_image_le (Set.toFinite _)
  have h3 : (Set.Iio μ).ncard = μ := by
    rw [← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]
  rw [hT.ncard_sharp] at h1
  omega

end Torus710

end CFSG.CGT.T75F
