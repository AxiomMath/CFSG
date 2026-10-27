module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.RootSL2.Adjust

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Dickson.Sec6.I1431.RootSL2
open scoped MatrixGroups

theorem excres_ringEquiv_eq_id_of_trace {K : Type} [Field K] (c : ℕ) (σ : K ≃+* K)
    (h3 : ∀ x, σ (σ (σ x)) = x)
    (hg : ∀ t : K, t ≠ 0 → (t + t⁻¹) ^ 2 + (c : K) * (t + t⁻¹) =
      (σ t + (σ t)⁻¹) ^ 2 + (c : K) * (σ t + (σ t)⁻¹)) : ∀ x, σ x = x := by
  have key : ∀ t : K, t ≠ 0 → σ (t + t⁻¹) = t + t⁻¹ := by
    intro t ht
    have hs : σ (t + t⁻¹) = σ t + (σ t)⁻¹ := by rw [map_add, map_inv₀]
    have h := hg t ht
    set u := t + t⁻¹ with hu
    set s := σ u with hsdef
    have hs' : s = σ t + (σ t)⁻¹ := hs
    rw [← hs'] at h
    have hfac : (u - s) * (u + s + (c : K)) = 0 := by linear_combination h
    rcases mul_eq_zero.1 hfac with h1 | h1
    · exact (sub_eq_zero.1 h1).symm
    · have hs2 : s = -(c : K) - u := by linear_combination h1
      have hss : σ s = u := by
        rw [hs2, map_sub, map_neg, map_natCast, ← hsdef]
        linear_combination (-1 : K) * hs2
      have := h3 u
      rw [← hsdef, hss] at this
      exact this
  intro x
  by_cases hx : x = 0
  · rw [hx, map_zero]
  have hk := key x hx
  rw [map_add, map_inv₀] at hk
  have hy : σ x ≠ 0 := (map_ne_zero σ).2 hx
  have hfac : (σ x - x) * (1 - (x * σ x)⁻¹) = 0 := by
    have e : (σ x - x) * (1 - (x * σ x)⁻¹) = (σ x + (σ x)⁻¹) - (x + x⁻¹) := by
      field_simp
      ring
    rw [e, hk, sub_self]
  rcases mul_eq_zero.1 hfac with h1 | h1
  · exact sub_eq_zero.1 h1
  · have h2 : x * σ x = 1 := by
      have : (x * σ x)⁻¹ = 1 := by linear_combination -h1
      exact inv_eq_one.1 this
    have h3' : σ x = x⁻¹ := eq_inv_of_mul_eq_one_right h2
    have h4 : σ (σ x) = x := by rw [h3', map_inv₀, h3', inv_inv]
    have := h3 x
    rw [h4] at this
    exact this

section Main

variable {K : Type} [Field K] [Finite K] {G : Type} [Group G] [Finite G] {ρ : SL(2, K) →* G}

theorem excres_normalizer_inner
    (hker : ∀ g : SL(2, K), ρ g = 1 → ∃ l : Kˣ, l ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) K) = (l : K) • (1 : Matrix (Fin 2) (Fin 2) K))
    {E : Type} [Field E] (ε : K →+* E) (c : ℕ) (c₀ : E) (χ : G → E)
    (hχ : ∀ g h : G, χ (h * g * h⁻¹) = χ g)
    (hχd : ∀ t : Kˣ, χ (ρ (sl2Diag K t)) =
      ε (((t : K) + (t : K)⁻¹) ^ 2 + (c : K) * ((t : K) + (t : K)⁻¹)) + c₀)
    {y₀ : G} (hy3 : y₀ ^ 3 = 1)
    (hJ : ρ.range.map (MulAut.conj y₀).toMonoidHom = ρ.range) :
    ∃ w ∈ ρ.range, ∀ j ∈ ρ.range, y₀ * j * y₀⁻¹ = w * j * w⁻¹ := by
  set η : MulAut G := MulAut.conj y₀ with hηdef
  have hη3 : ∀ x, η (η (η x)) = x := by
    intro x
    have hy3' : y₀ * y₀ * y₀ = 1 := by rw [← hy3, pow_succ, pow_succ, pow_one]
    simp only [hηdef, MulAut.conj_apply]
    calc y₀ * (y₀ * (y₀ * x * y₀⁻¹) * y₀⁻¹) * y₀⁻¹
        = (y₀ * y₀ * y₀) * x * (y₀ * y₀ * y₀)⁻¹ := by group
      _ = x := by rw [hy3']; group
  obtain ⟨v, hv, hα⟩ := exists_pairAut_adjust hker hJ
  obtain ⟨f, hf⟩ : ∃ f : K → K, ∀ c, (MulAut.conj v * η) (ρ (sl2Upper K c)) =
      ρ (sl2Upper K (f c)) := by
    choose f hf using exists_sl2Upper_param hα
    exact ⟨f, hf⟩
  obtain ⟨g, hg⟩ : ∃ g : K → K, ∀ c, (MulAut.conj v * η) (ρ (sl2Lower K c)) =
      ρ (sl2Lower K (g c)) := by
    choose g hg using exists_sl2Lower_param hα
    exact ⟨g, hg⟩
  obtain ⟨a, σ, hfa, hga, hd⟩ := exists_semilinear_params hker hα hf hg
  set α : MulAut G := MulAut.conj v * η with hαdef
  have hJη : ∀ y ∈ ρ.range, η y ∈ ρ.range := fun y hy => by
    have : η y ∈ ρ.range.map η.toMonoidHom := Subgroup.mem_map_of_mem _ hy
    rwa [hJ] at this
  set e : G := v * η v * η (η v) with hedef
  have hα3 : ∀ x, α (α (α x)) = e * x * e⁻¹ := by
    intro x
    simp only [hαdef, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hη3, hedef]
    group
  have hX3 : ∀ c, e * ρ (sl2Upper K c) * e⁻¹ =
      ρ (sl2Upper K ((a : K) * σ ((a : K) * σ ((a : K) * σ c)))) := by
    intro c
    rw [← hα3, hf, hfa, hf, hfa, hf, hfa]
  have he : e ∈ ρ.range := mul_mem (mul_mem hv (hJη _ hv)) (hJη _ (hJη _ hv))
  obtain ⟨p, hp⟩ := exists_sq_of_conj_upper hker he
    (μ := fun c => (a : K) * σ ((a : K) * σ ((a : K) * σ c))) hX3
  have hexp : ∀ c, (a : K) * σ ((a : K) * σ ((a : K) * σ c)) =
      ((a : K) * σ a * σ (σ a)) * σ (σ (σ c)) := by
    intro c
    simp only [map_mul]
    ring
  have hN : (a : K) * σ a * σ (σ a) = (p : K) ^ 2 := by
    have h1 := hp 1
    rw [hexp, map_one, map_one, map_one, mul_one, mul_one] at h1
    exact h1
  have hσ3 : ∀ x, σ (σ (σ x)) = x := by
    intro x
    have h1 := hp x
    rw [hexp, hN] at h1
    have hp2 : (p : K) ^ 2 ≠ 0 := pow_ne_zero 2 p.ne_zero
    exact mul_left_cancel₀ hp2 h1
  have hconj : ∀ t : Kˣ, χ (ρ (sl2Diag K (Units.map σ.toMonoidHom t))) = χ (ρ (sl2Diag K t)) := by
    intro t
    rw [← hd t]
    simp only [hαdef, MulAut.mul_apply, MulAut.conj_apply, hηdef]
    rw [hχ _ v]
    simpa using hχ (ρ (sl2Diag K t)) y₀
  have htrace : ∀ t : Kˣ, ((t : K) + (t : K)⁻¹) ^ 2 + (c : K) * ((t : K) + (t : K)⁻¹) =
      (σ (t : K) + (σ (t : K))⁻¹) ^ 2 + (c : K) * (σ (t : K) + (σ (t : K))⁻¹) := by
    intro t
    have h1 := hconj t
    rw [hχd, hχd] at h1
    have h2 := add_right_cancel h1
    have h3 := ε.injective h2
    simp only [Units.coe_map, Units.val_inv_eq_inv_val] at h3
    exact h3.symm
  have hσ : ∀ x, σ x = x := excres_ringEquiv_eq_id_of_trace c σ hσ3 fun t ht => by
    simpa using htrace (Units.mk0 t ht)
  have hN3 : (a : K) ^ 3 = (p : K) ^ 2 := by
    simp only [hσ] at hN
    linear_combination hN
  obtain ⟨r, hr2⟩ : ∃ r : Kˣ, (r : K) ^ 2 = (a : K) := by
    refine ⟨a ^ 2 * p⁻¹, ?_⟩
    have ha : (a : K) ≠ 0 := a.ne_zero
    have hp0 : (p : K) ≠ 0 := p.ne_zero
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    field_simp
    linear_combination hN3
  have hx' : ∀ c, α (ρ (sl2Upper K c)) = ρ (sl2Upper K ((r : K) ^ 2 * c)) := by
    intro c
    rw [hf, hfa, hr2, hσ]
  have hy' : ∀ c, α (ρ (sl2Lower K c)) = ρ (sl2Lower K (((r⁻¹ : Kˣ) : K) ^ 2 * c)) := by
    intro c
    rw [hg, hga, hσ]
    congr 2
    rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, inv_pow, hr2]
  have hconjd := eq_conj_diag (ρ := ρ) (α := α) (r := r) hx' hy'
  refine ⟨v⁻¹ * ρ (sl2Diag K r), mul_mem (inv_mem hv) ⟨_, rfl⟩, fun j hj => ?_⟩
  have h1 := hconjd j hj
  have h2 : α j = v * η j * v⁻¹ := rfl
  rw [h2] at h1
  have h3 : η j = y₀ * j * y₀⁻¹ := rfl
  rw [h3] at h1
  calc y₀ * j * y₀⁻¹ = v⁻¹ * (v * (y₀ * j * y₀⁻¹) * v⁻¹) * v := by group
    _ = v⁻¹ * (ρ (sl2Diag K r) * j * (ρ (sl2Diag K r))⁻¹) * v := by rw [h1]
    _ = (v⁻¹ * ρ (sl2Diag K r)) * j * (v⁻¹ * ρ (sl2Diag K r))⁻¹ := by group

end Main

end CFSG.HardMathSupport.Dickson.Sec6.I1431
