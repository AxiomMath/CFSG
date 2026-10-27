module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4CoreA

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

private lemma y4_d_B {Γ : Type*} [Group Γ] {V : Subgroup Γ} {x j₁ v : Γ}
    (hxj₁ : x * j₁ * x⁻¹ = j₁) (hxV : ∀ v ∈ V, x * v * x⁻¹ = v) (hv : v ∈ V) :
    x * (j₁ * v) * x⁻¹ * (j₁ * v)⁻¹ = 1 := by
  calc
    x * (j₁ * v) * x⁻¹ * (j₁ * v)⁻¹
        = (x * j₁ * x⁻¹) * (x * v * x⁻¹) * (v⁻¹ * j₁⁻¹) := by group
    _ = j₁ * v * (v⁻¹ * j₁⁻¹) := by rw [hxj₁, hxV v hv]
    _ = 1 := by group

private lemma y4_d_C {Γ : Type*} [Group Γ] {J V : Subgroup Γ} {x j₀ j₁ v : Γ}
    (hxj₀ : x * j₀ * x⁻¹ = j₀⁻¹) (hxj₁ : x * j₁ * x⁻¹ = j₁)
    (hxV : ∀ v ∈ V, x * v * x⁻¹ = v) (hj₀J : j₀ ∈ J)
    (hJsq : ∀ j ∈ J, j * j ∈ V) (hVsq : ∀ v ∈ V, v * v = 1) (hv : v ∈ V) :
    x * ((j₀ * j₁) * v) * x⁻¹ * ((j₀ * j₁) * v)⁻¹ = j₀ * j₀ := by
  calc
    x * ((j₀ * j₁) * v) * x⁻¹ * ((j₀ * j₁) * v)⁻¹
        = (x * j₀ * x⁻¹) * (x * j₁ * x⁻¹) * (x * v * x⁻¹) *
            (v⁻¹ * j₁⁻¹ * j₀⁻¹) := by group
    _ = j₀⁻¹ * j₁ * v * (v⁻¹ * j₁⁻¹ * j₀⁻¹) := by rw [hxj₀, hxj₁, hxV v hv]
    _ = j₀⁻¹ * j₀⁻¹ := by group
    _ = j₀ * j₀ := by
        rw [← mul_inv_rev]
        exact inv_eq_of_mul_eq_one_right (hVsq (j₀ * j₀) (hJsq j₀ hj₀J))

private lemma y4_sq_of_mem_coset {Γ : Type*} [Group Γ] {J V : Subgroup Γ} {j₁ g : Γ}
    (hJc : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a) (hVJ : V ≤ J) (hj₁J : j₁ ∈ J)
    (hVsq : ∀ v ∈ V, v * v = 1) (h : j₁⁻¹ * g ∈ V) : g * g = j₁ * j₁ := by
  have hw : j₁⁻¹ * g ∈ V := h
  have hgw : g = j₁ * (j₁⁻¹ * g) := by group
  rw [hgw]
  have hcomm : (j₁⁻¹ * g) * j₁ = j₁ * (j₁⁻¹ * g) := hJc _ (hVJ hw) _ hj₁J
  calc
    (j₁ * (j₁⁻¹ * g)) * (j₁ * (j₁⁻¹ * g)) =
        j₁ * ((j₁⁻¹ * g) * j₁) * (j₁⁻¹ * g) := by group
    _ = j₁ * (j₁ * (j₁⁻¹ * g)) * (j₁⁻¹ * g) := by rw [hcomm]
    _ = (j₁ * j₁) * ((j₁⁻¹ * g) * (j₁⁻¹ * g)) := by group
    _ = j₁ * j₁ := by rw [hVsq (j₁⁻¹ * g) hw]; group

private lemma y4_conj_prod {Γ : Type*} [Group Γ] {x₁ x₂ x₃ j₀ d₁ d₂ d₃ : Γ}
    (hx₁ : x₁ * j₀ * x₁⁻¹ = d₁ * j₀) (hx₂ : x₂ * j₀ * x₂⁻¹ = d₂ * j₀)
    (hx₃ : x₃ * j₀ * x₃⁻¹ = d₃ * j₀)
    (hx₂d₃ : x₂ * d₃ * x₂⁻¹ = d₃)
    (hx₁d₂ : x₁ * d₂ * x₁⁻¹ = d₂) (hx₁d₃ : x₁ * d₃ * x₁⁻¹ = d₃) :
    x₁ * x₂ * x₃ * j₀ * (x₁ * x₂ * x₃)⁻¹ * j₀⁻¹ = d₃ * d₂ * d₁ := by
  have hx₁d₃d₂ : x₁ * (d₃ * d₂) * x₁⁻¹ = d₃ * d₂ := by
    rw [show x₁ * (d₃ * d₂) * x₁⁻¹ = (x₁ * d₃ * x₁⁻¹) * (x₁ * d₂ * x₁⁻¹) by group,
      hx₁d₃, hx₁d₂]
  have hx₂d₃j : x₂ * (d₃ * j₀) * x₂⁻¹ = d₃ * (x₂ * j₀ * x₂⁻¹) := by
    rw [show x₂ * (d₃ * j₀) * x₂⁻¹ = (x₂ * d₃ * x₂⁻¹) * (x₂ * j₀ * x₂⁻¹) by group,
      hx₂d₃]
  calc
    x₁ * x₂ * x₃ * j₀ * (x₁ * x₂ * x₃)⁻¹ * j₀⁻¹
        = x₁ * (x₂ * (x₃ * j₀ * x₃⁻¹) * x₂⁻¹) * x₁⁻¹ * j₀⁻¹ := by group
    _ = x₁ * (x₂ * (d₃ * j₀) * x₂⁻¹) * x₁⁻¹ * j₀⁻¹ := by rw [hx₃]
    _ = x₁ * (d₃ * (x₂ * j₀ * x₂⁻¹)) * x₁⁻¹ * j₀⁻¹ := by rw [hx₂d₃j]
    _ = x₁ * (d₃ * (d₂ * j₀)) * x₁⁻¹ * j₀⁻¹ := by rw [hx₂]
    _ = (x₁ * (d₃ * d₂) * x₁⁻¹) * (x₁ * j₀ * x₁⁻¹) * j₀⁻¹ := by group
    _ = (d₃ * d₂) * (d₁ * j₀) * j₀⁻¹ := by rw [hx₁d₃d₂, hx₁]
    _ = d₃ * d₂ * d₁ := by group

theorem y4_core_comp {Γ : Type*} [Group Γ] {J V : Subgroup Γ} {α x k j₀ j₁ : Γ}
    (hVJ : V ≤ J) (hJc : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a)
    (hVsq : ∀ v ∈ V, v * v = 1) (hJsq : ∀ j ∈ J, j * j ∈ V) (hJ1 : ∀ j ∈ J, j * j = 1 → j ∈ V)
    (hα2 : α * α = 1) (hαJ : ∀ j ∈ J, α * j * α⁻¹ = j⁻¹)
    (hx2 : x * x = 1) (hxJ : ∀ j ∈ J, x * j * x⁻¹ ∈ J) (hxV : ∀ v ∈ V, x * v * x⁻¹ = v)
    (hj₀ : j₀ ∈ J) (hj₀V : j₀ ∉ V) (hxα : x * α * x⁻¹ = j₀ * α)
    (hj₁ : j₁ ∈ J) (hj₁V : j₁ ∉ V) (hxj₁ : x * j₁ * x⁻¹ = j₁)
    (hcov : ∀ j ∈ J, j ∈ V ∨ j₀⁻¹ * j ∈ V ∨ j₁⁻¹ * j ∈ V ∨ (j₀ * j₁)⁻¹ * j ∈ V)
    (hk3 : k ^ 3 = 1) (hkJ : ∀ j ∈ J, k * j * k⁻¹ ∈ J) (hkV : ∀ v ∈ V, k * v * k⁻¹ ∈ V)
    (hkfix : ∀ j ∈ J, k * j * k⁻¹ * j⁻¹ ∈ V → j ∈ V)
    (hprod : x * (k * x * k⁻¹) * (k ^ 2 * x * (k ^ 2)⁻¹) ∈ J ∨
      ∃ j ∈ J, x * (k * x * k⁻¹) * (k ^ 2 * x * (k ^ 2)⁻¹) = j * α) : False := by
  have hk2 : k ^ 2 = k⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    exact hk3
  have hk2inv : (k ^ 2)⁻¹ = k := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ]
    exact hk3
  have hkconj : ∀ v : Γ, k⁻¹ * v * k = k ^ 2 * v * (k ^ 2)⁻¹ := by
    intro v
    calc
      k⁻¹ * v * k = k⁻¹ * v * (k⁻¹)⁻¹ := by rw [inv_inv]
      _ = k ^ 2 * v * (k ^ 2)⁻¹ := by rw [hk2]
  have hxj₀ : x * j₀ * x⁻¹ = j₀⁻¹ := by
    have hα : x * (x * α * x⁻¹) * x⁻¹ = α := by
      rw [show x * (x * α * x⁻¹) * x⁻¹ = (x * x) * α * (x⁻¹ * x⁻¹) by group,
        hx2, one_mul]
      have : x⁻¹ * x⁻¹ = 1 := by
        rw [show x⁻¹ * x⁻¹ = (x * x)⁻¹ by group, hx2, inv_one]
      rw [this, mul_one]
    have hR : x * (j₀ * α) * x⁻¹ = (x * j₀ * x⁻¹) * (j₀ * α) := by
      rw [show x * (j₀ * α) * x⁻¹ = (x * j₀ * x⁻¹) * (x * α * x⁻¹) by group, hxα]
    have h1 : α = (x * j₀ * x⁻¹) * (j₀ * α) := by
      calc
        α = x * (x * α * x⁻¹) * x⁻¹ := hα.symm
        _ = x * (j₀ * α) * x⁻¹ := by rw [hxα]
        _ = (x * j₀ * x⁻¹) * (j₀ * α) := hR
    have h2 : (x * j₀ * x⁻¹) * j₀ = 1 := by
      have key := congrArg (fun t => t * α⁻¹) h1
      rw [mul_inv_cancel α] at key
      rw [show ((x * j₀ * x⁻¹) * (j₀ * α)) * α⁻¹ = (x * j₀ * x⁻¹) * j₀ by group] at key
      exact key.symm
    exact (eq_inv_iff_mul_eq_one).mpr h2
  have hkVinv : ∀ v ∈ V, k⁻¹ * v * k ∈ V := by
    intro v hv
    have h1 : k * v * k⁻¹ ∈ V := hkV v hv
    have h2 : k * (k * v * k⁻¹) * k⁻¹ ∈ V := hkV _ h1
    have heq : k * (k * v * k⁻¹) * k⁻¹ = k⁻¹ * v * k := by
      calc
        k * (k * v * k⁻¹) * k⁻¹ = (k * k) * v * (k * k)⁻¹ := by group
        _ = k ^ 2 * v * (k ^ 2)⁻¹ := by rw [pow_two]
        _ = k⁻¹ * v * k := (hkconj v).symm
    rwa [heq] at h2
  have hkJinv : ∀ j ∈ J, k⁻¹ * j * k ∈ J := by
    intro j hj
    have h1 : k * j * k⁻¹ ∈ J := hkJ j hj
    have h2 : k * (k * j * k⁻¹) * k⁻¹ ∈ J := hkJ _ h1
    have heq : k * (k * j * k⁻¹) * k⁻¹ = k⁻¹ * j * k := by
      calc
        k * (k * j * k⁻¹) * k⁻¹ = (k * k) * j * (k * k)⁻¹ := by group
        _ = k ^ 2 * j * (k ^ 2)⁻¹ := by rw [pow_two]
        _ = k⁻¹ * j * k := (hkconj j).symm
    rwa [heq] at h2
  have hk2V : ∀ v ∈ V, k ^ 2 * v * (k ^ 2)⁻¹ ∈ V := by
    intro v hv
    have h := hkVinv v hv
    have heq : k ^ 2 * v * (k ^ 2)⁻¹ = k⁻¹ * v * k := by rw [hk2inv, hk2]
    rwa [heq]
  have hx₂V : ∀ v ∈ V, (k * x * k⁻¹) * v * (k * x * k⁻¹)⁻¹ = v := by
    intro v hv
    have hv' : k⁻¹ * v * k ∈ V := hkVinv v hv
    calc
      (k * x * k⁻¹) * v * (k * x * k⁻¹)⁻¹
          = k * (x * (k⁻¹ * v * k) * x⁻¹) * k⁻¹ := by group
      _ = k * (k⁻¹ * v * k) * k⁻¹ := by rw [hxV _ hv']
      _ = v := by group
  set j' : Γ := k⁻¹ * j₀ * k with hj'def
  set j'' : Γ := (k ^ 2)⁻¹ * j₀ * k ^ 2 with hj''def
  have hj'J : j' ∈ J := by rw [hj'def]; exact hkJinv j₀ hj₀
  have hj''J : j'' ∈ J := by
    have heq : j'' = k * j₀ * k⁻¹ := by rw [hj''def, hk2inv, hk2]
    rw [heq]; exact hkJ j₀ hj₀
  have hj'k : j' = k ^ 2 * j₀ * k := by rw [hj'def, hk2]
  have hj'k2 : j' = k ^ 2 * j₀ * (k ^ 2)⁻¹ := by rw [hj'def]; exact hkconj j₀
  have hkj' : k * j' * k⁻¹ = j₀ := by rw [hj'def]; group
  have hkj'' : k * j'' * k⁻¹ = j' := by
    rw [hj''def, hk2inv, hj'k]
    calc
      k * (k * j₀ * k ^ 2) * k⁻¹ = (k * k) * j₀ * (k ^ 2 * k⁻¹) := by group
      _ = k ^ 2 * j₀ * (k ^ 2 * k⁻¹) := by rw [← pow_two]
      _ = k ^ 2 * j₀ * k := by rw [show k ^ 2 * k⁻¹ = k by rw [pow_two]; group]
  have hj'V : j' ∉ V := by
    intro h
    have h1 : k * j' * k⁻¹ ∈ V := hkV j' h
    rw [hkj'] at h1
    exact hj₀V h1
  have hj''V : j'' ∉ V := by
    intro h
    have hsq : j'' * j'' = 1 := hVsq j'' h
    have heq : j'' * j'' = (k ^ 2)⁻¹ * (j₀ * j₀) * k ^ 2 := by rw [hj''def]; group
    rw [heq] at hsq
    have hL : k ^ 2 * ((k ^ 2)⁻¹ * (j₀ * j₀) * k ^ 2) * (k ^ 2)⁻¹ = j₀ * j₀ := by
      group
    have hR : k ^ 2 * (1 : Γ) * (k ^ 2)⁻¹ = 1 := by group
    have key := congrArg (fun t => k ^ 2 * t * (k ^ 2)⁻¹) hsq
    rw [hL, hR] at key
    exact hj₀V (hJ1 j₀ hj₀ key)
  have hj'A : j₀⁻¹ * j' ∉ V := by
    intro h
    have h1 : k * (j₀⁻¹ * j') * k⁻¹ ∈ V := hkV _ h
    have heq : k * (j₀⁻¹ * j') * k⁻¹ = k * j₀⁻¹ * k⁻¹ * j₀ := by rw [hj'def]; group
    rw [heq] at h1
    exact hj₀V (V.inv_mem_iff.mp (hkfix j₀⁻¹ (J.inv_mem hj₀) (by simpa using h1)))
  have hj''A : j₀⁻¹ * j'' ∉ V := by
    intro h
    have h1 : j₀ * (j₀⁻¹ * j'') * j₀⁻¹ ∈ V := by
      have hcomm : j₀ * (j₀⁻¹ * j'') = (j₀⁻¹ * j'') * j₀ := hJc j₀ hj₀ _ (hVJ h)
      have heq : j₀ * (j₀⁻¹ * j'') * j₀⁻¹ = j₀⁻¹ * j'' := by rw [hcomm]; group
      rw [heq]; exact h
    have heq : j₀ * (j₀⁻¹ * j'') * j₀⁻¹ = k * j₀ * k⁻¹ * j₀⁻¹ := by
      rw [hj''def, hk2inv, hk2]; group
    rw [heq] at h1
    exact hj₀V (hkfix j₀ hj₀ h1)
  have hdiff : j'⁻¹ * j'' ∉ V := by
    intro h
    have h1 : k * (j'⁻¹ * j'') * k⁻¹ ∈ V := hkV _ h
    have heq : k * (j'⁻¹ * j'') * k⁻¹ = j₀⁻¹ * j' := by
      rw [show k * (j'⁻¹ * j'') * k⁻¹ = (k * j' * k⁻¹)⁻¹ * (k * j'' * k⁻¹) by group,
        hkj', hkj'']
    rw [heq] at h1
    exact hj'A h1
  have hj0j1V : j₀ * j₁ ∉ V := by
    intro h
    have h1 : x * (j₀ * j₁) * x⁻¹ * (j₀ * j₁)⁻¹ = 1 := by
      rw [hxV (j₀ * j₁) h]; group
    have h01 : x * (j₀ * j₁) * x⁻¹ * (j₀ * j₁)⁻¹ = j₀ * j₀ := by
      calc
        x * (j₀ * j₁) * x⁻¹ * (j₀ * j₁)⁻¹
            = (x * j₀ * x⁻¹) * (x * j₁ * x⁻¹) * (j₁⁻¹ * j₀⁻¹) := by group
        _ = j₀⁻¹ * j₁ * (j₁⁻¹ * j₀⁻¹) := by rw [hxj₀, hxj₁]
        _ = j₀⁻¹ * j₀⁻¹ := by group
        _ = j₀ * j₀ := by
            rw [← mul_inv_rev]
            exact inv_eq_of_mul_eq_one_right (hVsq (j₀ * j₀) (hJsq j₀ hj₀))
    rw [h01] at h1
    exact hj₀V (hJ1 j₀ hj₀ h1)
  have hcase : (j₁⁻¹ * j' ∈ V ∧ (j₀ * j₁)⁻¹ * j'' ∈ V) ∨
      ((j₀ * j₁)⁻¹ * j' ∈ V ∧ j₁⁻¹ * j'' ∈ V) := by
    have hj'cases : j₁⁻¹ * j' ∈ V ∨ (j₀ * j₁)⁻¹ * j' ∈ V := by
      rcases hcov j' hj'J with h | h | h | h
      · exact absurd h hj'V
      · exact absurd h hj'A
      · exact Or.inl h
      · exact Or.inr h
    have hj''cases : j₁⁻¹ * j'' ∈ V ∨ (j₀ * j₁)⁻¹ * j'' ∈ V := by
      rcases hcov j'' hj''J with h | h | h | h
      · exact absurd h hj''V
      · exact absurd h hj''A
      · exact Or.inl h
      · exact Or.inr h
    rcases hj'cases with h'B | h'C <;> rcases hj''cases with h''B | h''C
    · exfalso
      apply hdiff
      have hmem : (j₁⁻¹ * j')⁻¹ * (j₁⁻¹ * j'') ∈ V := V.mul_mem (V.inv_mem h'B) h''B
      have heq : (j₁⁻¹ * j')⁻¹ * (j₁⁻¹ * j'') = j'⁻¹ * j'' := by group
      rwa [heq] at hmem
    · exact Or.inl ⟨h'B, h''C⟩
    · exact Or.inr ⟨h'C, h''B⟩
    · exfalso
      apply hdiff
      have hmem : ((j₀ * j₁)⁻¹ * j')⁻¹ * ((j₀ * j₁)⁻¹ * j'') ∈ V :=
        V.mul_mem (V.inv_mem h'C) h''C
      have heq : ((j₀ * j₁)⁻¹ * j')⁻¹ * ((j₀ * j₁)⁻¹ * j'') = j'⁻¹ * j'' := by group
      rwa [heq] at hmem
  set d₁ : Γ := x * j₀ * x⁻¹ * j₀⁻¹ with hd₁def
  set d₂ : Γ := (k * x * k⁻¹) * j₀ * (k * x * k⁻¹)⁻¹ * j₀⁻¹ with hd₂def
  set d₃ : Γ := (k ^ 2 * x * (k ^ 2)⁻¹) * j₀ * (k ^ 2 * x * (k ^ 2)⁻¹)⁻¹ * j₀⁻¹
    with hd₃def
  set π : Γ := x * (k * x * k⁻¹) * (k ^ 2 * x * (k ^ 2)⁻¹) with hπdef
  have hd₁ : d₁ = j₀ * j₀ := by
    rw [hd₁def, hxj₀, ← mul_inv_rev]
    exact inv_eq_of_mul_eq_one_right (hVsq (j₀ * j₀) (hJsq j₀ hj₀))
  have hd₂j : d₂ = k * (x * j' * x⁻¹ * j'⁻¹) * k⁻¹ := by
    rw [hd₂def, hj'def]; group
  have hd₃j : d₃ = k ^ 2 * (x * j'' * x⁻¹ * j''⁻¹) * (k ^ 2)⁻¹ := by
    rw [hd₃def, hj''def]; group
  have hd₂V : d₂ ∈ V := by
    rw [hd₂j]
    exact hkV _ (y4_lam_mem hJc hJsq hJ1 hxJ hxV j' hj'J)
  have hd₃V : d₃ ∈ V := by
    rw [hd₃j]
    exact hk2V _ (y4_lam_mem hJc hJsq hJ1 hxJ hxV j'' hj''J)
  have hEgen : π * j₀ * π⁻¹ * j₀⁻¹ = d₃ * d₂ * d₁ := by
    rw [hπdef]
    refine y4_conj_prod ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hd₁def]; group
    · rw [hd₂def]; group
    · rw [hd₃def]; group
    · exact hx₂V d₃ hd₃V
    · exact hxV d₂ hd₂V
    · exact hxV d₃ hd₃V
  have hE : π * j₀ * π⁻¹ * j₀⁻¹ = j₀ * j₀ * (j₁ * j₁) := by
    rw [hEgen]
    rcases hcase with ⟨h'B, h''C⟩ | ⟨h'C, h''B⟩
    ·
      have hdj' : x * j' * x⁻¹ * j'⁻¹ = 1 := by
        have hv : j₁⁻¹ * j' ∈ V := h'B
        have h : j' = j₁ * (j₁⁻¹ * j') := by group
        rw [h]
        exact y4_d_B hxj₁ hxV hv
      have hdj'' : x * j'' * x⁻¹ * j''⁻¹ = j₀ * j₀ := by
        have hv : (j₀ * j₁)⁻¹ * j'' ∈ V := h''C
        have h : j'' = (j₀ * j₁) * ((j₀ * j₁)⁻¹ * j'') := by group
        rw [h]
        exact y4_d_C hxj₀ hxj₁ hxV hj₀ hJsq hVsq hv
      have hd₂val : d₂ = 1 := by
        rw [hd₂j, hdj', mul_one]; group
      have hd₃val : d₃ = j' * j' := by
        rw [hd₃j, hdj'']
        rw [show k ^ 2 * (j₀ * j₀) * (k ^ 2)⁻¹ =
            (k ^ 2 * j₀ * (k ^ 2)⁻¹) * (k ^ 2 * j₀ * (k ^ 2)⁻¹) by group]
        rw [← hj'k2]
      have hj'sq : j' * j' = j₁ * j₁ := y4_sq_of_mem_coset hJc hVJ hj₁ hVsq h'B
      rw [hd₃val, hd₂val, hd₁, hj'sq]
      simp only [mul_one]
      exact hJc (j₁ * j₁) (hVJ (hJsq j₁ hj₁)) (j₀ * j₀) (hVJ (hJsq j₀ hj₀))
    ·
      have hdj' : x * j' * x⁻¹ * j'⁻¹ = j₀ * j₀ := by
        have hv : (j₀ * j₁)⁻¹ * j' ∈ V := h'C
        have h : j' = (j₀ * j₁) * ((j₀ * j₁)⁻¹ * j') := by group
        rw [h]
        exact y4_d_C hxj₀ hxj₁ hxV hj₀ hJsq hVsq hv
      have hdj'' : x * j'' * x⁻¹ * j''⁻¹ = 1 := by
        have hv : j₁⁻¹ * j'' ∈ V := h''B
        have h : j'' = j₁ * (j₁⁻¹ * j'') := by group
        rw [h]
        exact y4_d_B hxj₁ hxV hv
      have hj''sq' : j'' * j'' = k * (j₀ * j₀) * k⁻¹ := by
        rw [hj''def]
        rw [show ((k ^ 2)⁻¹ * j₀ * k ^ 2) * ((k ^ 2)⁻¹ * j₀ * k ^ 2) =
            (k ^ 2)⁻¹ * (j₀ * j₀) * k ^ 2 by group]
        rw [hk2inv, hk2]
      have hd₂val : d₂ = j'' * j'' := by
        rw [hd₂j, hdj', ← hj''sq']
      have hd₃val : d₃ = 1 := by
        rw [hd₃j, hdj'', mul_one]; group
      have hj''sq : j'' * j'' = j₁ * j₁ := y4_sq_of_mem_coset hJc hVJ hj₁ hVsq h''B
      rw [hd₃val, hd₂val, hd₁, hj''sq]
      simp only [one_mul]
      exact hJc (j₁ * j₁) (hVJ (hJsq j₁ hj₁)) (j₀ * j₀) (hVJ (hJsq j₀ hj₀))
  rcases hprod with hπJ | ⟨j, hjJ, hjα⟩
  · have hcomm : π * j₀ = j₀ * π := hJc π hπJ j₀ hj₀
    have hE1 : π * j₀ * π⁻¹ * j₀⁻¹ = 1 := by rw [hcomm]; group
    rw [hE] at hE1
    have hj01sq : (j₀ * j₁) * (j₀ * j₁) = 1 := by
      rw [show (j₀ * j₁) * (j₀ * j₁) = j₀ * j₀ * (j₁ * j₁) by
        calc
          (j₀ * j₁) * (j₀ * j₁) = j₀ * (j₁ * j₀) * j₁ := by group
          _ = j₀ * (j₀ * j₁) * j₁ := by rw [hJc j₁ hj₁ j₀ hj₀]
          _ = j₀ * j₀ * (j₁ * j₁) := by group]
      exact hE1
    exact hj0j1V (hJ1 (j₀ * j₁) (J.mul_mem hj₀ hj₁) hj01sq)
  · have hconj : π * j₀ * π⁻¹ = j₀⁻¹ := by
      rw [hjα]
      rw [show (j * α) * j₀ * (j * α)⁻¹ = j * (α * j₀ * α⁻¹) * j⁻¹ by group,
        hαJ j₀ hj₀]
      rw [show j * j₀⁻¹ * j⁻¹ = j₀⁻¹ by
        rw [hJc j hjJ j₀⁻¹ (J.inv_mem hj₀)]; group]
    have hE1 : π * j₀ * π⁻¹ * j₀⁻¹ = j₀ * j₀ := by
      rw [hconj]
      rw [show j₀⁻¹ * j₀⁻¹ = j₀ * j₀ by
        rw [← mul_inv_rev]
        exact inv_eq_of_mul_eq_one_right (hVsq (j₀ * j₀) (hJsq j₀ hj₀))]
    rw [hE] at hE1
    have hj1sq : j₁ * j₁ = 1 := by
      have key : (j₀ * j₀)⁻¹ * (j₀ * j₀ * (j₁ * j₁)) = (j₀ * j₀)⁻¹ * (j₀ * j₀) :=
        congrArg (fun t => (j₀ * j₀)⁻¹ * t) hE1
      have hL : (j₀ * j₀)⁻¹ * (j₀ * j₀ * (j₁ * j₁)) = j₁ * j₁ := by group
      have hR : (j₀ * j₀)⁻¹ * (j₀ * j₀) = 1 := by group
      rw [hL, hR] at key
      exact key
    exact hj₁V (hJ1 j₁ hj₁ hj1sq)

end CFSG.OddStandard.HigherRank.YamadaG23
