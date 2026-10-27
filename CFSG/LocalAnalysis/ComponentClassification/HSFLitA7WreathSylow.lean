module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Wreath

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer DihedralGroup
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

namespace A7Data

variable {t : X} {L : Subgroup X} (A : A7Data t L)

omit [Finite X] in
theorem commute_zt_of_coords {z : X} (hz : z ∈ A.T)
    (φ : A.T ≃* DihedralGroup 4 × DihedralGroup 4) (hφz : φ ⟨z, hz⟩ = (r 2, 1))
    (hφt : φ ⟨t, A.t_mem_T⟩ = (1, r 2)) {h : X} (hh : h ∈ A.T) : z * t * h = h * (z * t) := by
  have hφzt : φ ⟨z * t, mul_mem hz A.t_mem_T⟩ = (r 2, r 2) := by
    have : (⟨z * t, mul_mem hz A.t_mem_T⟩ : A.T) = ⟨z, hz⟩ * ⟨t, A.t_mem_T⟩ := rfl
    rw [this, map_mul, hφz, hφt]
    rfl
  have : (⟨z * t, mul_mem hz A.t_mem_T⟩ : A.T) * ⟨h, hh⟩ =
      ⟨h, hh⟩ * ⟨z * t, mul_mem hz A.t_mem_T⟩ :=
    φ.injective (by rw [map_mul, map_mul, hφzt, dd_r_two_r_two_central])
  exact congrArg Subtype.val this

omit [Finite X] in
theorem z_ne_t_of_coords {z : X} (hz : z ∈ A.T)
    (φ : A.T ≃* DihedralGroup 4 × DihedralGroup 4) (hφz : φ ⟨z, hz⟩ = (r 2, 1))
    (hφt : φ ⟨t, A.t_mem_T⟩ = (1, r 2)) : z ≠ t := by
  intro h
  have : φ ⟨z, hz⟩ = φ ⟨t, A.t_mem_T⟩ := by congr 1; exact Subtype.ext h
  rw [hφz, hφt] at this
  exact absurd this (by decide)

omit [Finite X] in
theorem sq_z_of_coords {z : X} (hz : z ∈ A.T) (φ : A.T ≃* DihedralGroup 4 × DihedralGroup 4)
    (hφz : φ ⟨z, hz⟩ = (r 2, 1)) : z ^ 2 = 1 := by
  have : (⟨z, hz⟩ : A.T) ^ 2 = 1 := φ.injective (by rw [map_pow, hφz, map_one]; decide)
  exact congrArg Subtype.val this

theorem exists_sylow_sup {z : X} (hz : z ∈ A.T) (φ : A.T ≃* DihedralGroup 4 × DihedralGroup 4)
    (hφz : φ ⟨z, hz⟩ = (r 2, 1)) (hφt : φ ⟨t, A.t_mem_T⟩ = (1, r 2)) {x : X} (hx : x ∈ A.T)
    (hx2 : x ^ 2 = z) {u : X} (hu2 : u ^ 2 = 1) (huN : u ∈ normalizer (A.T : Set X))
    (hup : IsPGroup 2 (A.T ⊔ zpowers u : Subgroup X)) (huz : u * z * u⁻¹ = t)
    (hut : u * t * u⁻¹ = z) : ∃ S : Sylow 2 X, (S : Subgroup X) = A.T ⊔ zpowers u := by
  by_contra hne
  push Not at hne
  obtain ⟨w', hw'N, hw'T, hw'p⟩ := exists_mem_normalizer_not_mem hup hne
  set T₁ : Subgroup X := A.T ⊔ zpowers u with hT₁
  have huinv : u⁻¹ = u := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hu2]
  have huT₁ : u ∈ T₁ := mem_sup_right (mem_zpowers u)
  have hut' : u⁻¹ * t * u = z := by rw [← hut, huinv]
  have huz' : u⁻¹ * z * u = t := by rw [← huz, huinv]
  have hmem : ∀ h ∈ T₁, h ∈ A.T ∨ h * u ∈ A.T := fun h hh =>
    mem_or_mul_mem_of_mem_sup_zpowers hu2 huN hh
  have hzT : ∀ h ∈ A.T, z * h = h * z := by
    intro h hh
    have h1 := A.commute_zt_of_coords hz φ hφz hφt hh
    have h2 := A.commute_t hh
    calc z * h = z * t * h * t⁻¹ := by rw [mul_assoc z t h, h2.symm]; group
      _ = h * (z * t) * t⁻¹ := by rw [h1]
      _ = h * z := by group
  have hz2 := A.sq_z_of_coords hz φ hφz
  have hzt_ne : z ≠ t := A.z_ne_t_of_coords hz φ hφz hφt
  have ht2 : t ^ 2 = 1 := by rw [← A.orderOf_t, pow_orderOf_eq_one]
  have hζ2 : (z * t) ^ 2 = 1 := by
    calc (z * t) ^ 2 = z * (t * z) * t := by rw [pow_two]; group
      _ = z * (z * t) * t := by rw [← A.commute_t hz]
      _ = z ^ 2 * t ^ 2 := by rw [pow_two, pow_two]; group
      _ = 1 := by rw [hz2, ht2, one_mul]
  have hζu : z * t * u = u * (z * t) := by
    have : u * (z * t) * u⁻¹ = z * t := by
      rw [show u * (z * t) * u⁻¹ = (u * z * u⁻¹) * (u * t * u⁻¹) by group, huz, hut,
        A.commute_t hz]
    calc z * t * u = u * (z * t) * u⁻¹ * u := by rw [this]
      _ = u * (z * t) := by group
  have hζc : ∀ h ∈ T₁, z * t * h = h * (z * t) := by
    intro h hh
    rcases hmem h hh with h1 | h1
    · exact A.commute_zt_of_coords hz φ hφz hφt h1
    · have h2 := A.commute_zt_of_coords hz φ hφz hφt h1
      calc z * t * h = z * t * (h * u) * u⁻¹ := by group
        _ = h * u * (z * t) * u⁻¹ := by rw [h2]
        _ = h * (u * (z * t)) * u⁻¹ := by group
        _ = h * (z * t * u) * u⁻¹ := by rw [hζu]
        _ = h * (z * t) := by group
  have hcen : ∀ g ∈ T₁, (∀ h ∈ T₁, g * h = h * g) → g = 1 ∨ g = z * t := by
    intro g hg hgc
    have hgT : g ∈ A.T := by
      rcases hmem g hg with h1 | h1
      · exact h1
      · exfalso
        have h2 : g * t * g⁻¹ = z := by
          have h3 := hzT _ h1
          calc g * t * g⁻¹ = (g * u) * (u⁻¹ * t * u) * (g * u)⁻¹ := by group
            _ = (g * u) * z * (g * u)⁻¹ := by rw [hut']
            _ = z := by rw [← h3]; group
        have h4 := hgc t (mem_sup_left A.t_mem_T)
        exact hzt_ne (by rw [← h2, h4]; group)
    rcases A.eq_of_central_of_coords hz φ hφz hφt hgT (fun h hh => hgc h (mem_sup_left hh))
      with h | h | h | h
    · exact Or.inl h
    · exfalso
      have h4 := hgc u huT₁
      rw [h] at h4
      have : t = z := by
        rw [← huz]
        calc u * z * u⁻¹ = z * u * u⁻¹ := by rw [h4]
          _ = z := by group
      exact hzt_ne this.symm
    · exfalso
      have h4 := hgc u huT₁
      rw [h] at h4
      have : z = t := by
        rw [← hut]
        calc u * t * u⁻¹ = t * u * u⁻¹ := by rw [h4]
          _ = t := by group
      exact hzt_ne this
    · exact Or.inr h
  have hw'ζ : w' * (z * t) * w'⁻¹ = z * t := by
    have hm : w' * (z * t) * w'⁻¹ ∈ T₁ :=
      (mem_normalizer_iff.mp hw'N _).mp (mul_mem (mem_sup_left hz) (mem_sup_left A.t_mem_T))
    rcases hcen _ hm (fun h hh => by
      have hh' : w'⁻¹ * h * w' ∈ T₁ := by
        have := (mem_normalizer_iff.mp (inv_mem hw'N) h).mp hh
        rwa [inv_inv] at this
      have := hζc _ hh'
      calc w' * (z * t) * w'⁻¹ * h = w' * (z * t * (w'⁻¹ * h * w')) * w'⁻¹ := by group
        _ = w' * ((w'⁻¹ * h * w') * (z * t)) * w'⁻¹ := by rw [this]
        _ = h * (w' * (z * t) * w'⁻¹) := by group) with h | h
    · exfalso
      have : z * t = 1 := by
        calc z * t = w'⁻¹ * (w' * (z * t) * w'⁻¹) * w' := by group
          _ = 1 := by rw [h]; group
      exact hzt_ne (by
        calc z = z * t * t := by rw [mul_assoc, ← pow_two, ht2, mul_one]
          _ = t := by rw [this, one_mul])
    · exact h
  have htc : ∀ h ∈ T₁, t * h * t⁻¹ * h⁻¹ = 1 ∨ t * h * t⁻¹ * h⁻¹ = z * t := by
    intro h hh
    rcases hmem h hh with h1 | h1
    · left
      rw [← A.commute_t h1]
      group
    · right
      have h3 := hzT _ h1
      calc t * h * t⁻¹ * h⁻¹ = t * (h * u) * (u⁻¹ * t⁻¹ * u) * (h * u)⁻¹ := by group
        _ = t * (h * u) * z⁻¹ * (h * u)⁻¹ := by
            rw [show u⁻¹ * t⁻¹ * u = (u⁻¹ * t * u)⁻¹ by group, hut']
        _ = t * z⁻¹ := by
            rw [show z⁻¹ = z by rw [inv_eq_iff_mul_eq_one, ← pow_two, hz2], mul_assoc t,
              ← h3]; group
        _ = z * t := by
            rw [show z⁻¹ = z by rw [inv_eq_iff_mul_eq_one, ← pow_two, hz2], A.commute_t hz]
  set t' := w' * t * w'⁻¹ with ht'
  have ht'T₁ : t' ∈ T₁ := (mem_normalizer_iff.mp hw'N _).mp (mem_sup_left A.t_mem_T)
  have ht'c : ∀ h ∈ T₁, t' * h * t'⁻¹ * h⁻¹ = 1 ∨ t' * h * t'⁻¹ * h⁻¹ = z * t := by
    intro h hh
    have hh' : w'⁻¹ * h * w' ∈ T₁ := by
      have := (mem_normalizer_iff.mp (inv_mem hw'N) h).mp hh
      rwa [inv_inv] at this
    have heq : t' * h * t'⁻¹ * h⁻¹ =
        w' * (t * (w'⁻¹ * h * w') * t⁻¹ * (w'⁻¹ * h * w')⁻¹) * w'⁻¹ := by rw [ht']; group
    rcases htc _ hh' with h1 | h1
    · left
      rw [heq, h1]
      group
    · right
      rw [heq, h1, hw'ζ]
  have ht'zt : t' = z ∨ t' = t := by
    rcases hmem t' ht'T₁ with h1 | h1
    · rcases A.eq_of_commutator_of_coords hz φ hφz hφt h1 (fun h hh => ht'c h (mem_sup_left hh))
        with h | h | h | h
      · exact absurd h (A.conj_t_ne_one w')
      · exact Or.inl h
      · exact Or.inr h
      · exfalso
        have : t = z * t := by
          calc t = w'⁻¹ * t' * w' := by rw [ht']; group
            _ = w'⁻¹ * (w' * (z * t) * w'⁻¹) * w' := by rw [h, hw'ζ]
            _ = z * t := by group
        have hz1 : z = 1 := by
          calc z = z * t * t⁻¹ := by group
            _ = 1 := by rw [← this]; group
        exact A.z_ne_one_of_coords hz φ hφz hz1
    · exfalso
      have h3 : t' * z * t'⁻¹ = t := by
        have h4 := A.commute_t h1
        calc t' * z * t'⁻¹ = (t' * u) * (u⁻¹ * z * u) * (t' * u)⁻¹ := by group
          _ = (t' * u) * t * (t' * u)⁻¹ := by rw [huz']
          _ = t := by rw [h4]; group
      have h5 : (t' * x * t'⁻¹) ^ 2 = t := by rw [conj_pow, hx2, h3]
      rcases ht'c x (mem_sup_left hx) with h6 | h6
      · have : t' * x * t'⁻¹ = x := by
          calc t' * x * t'⁻¹ = t' * x * t'⁻¹ * x⁻¹ * x := by group
            _ = x := by rw [h6, one_mul]
        rw [this, hx2] at h5
        exact hzt_ne h5
      · have : t' * x * t'⁻¹ = z * t * x := by
          calc t' * x * t'⁻¹ = t' * x * t'⁻¹ * x⁻¹ * x := by group
            _ = z * t * x := by rw [h6]
        rw [this] at h5
        have h7 : (z * t * x) ^ 2 = x ^ 2 := by
          have hc := hζc x (mem_sup_left hx)
          calc (z * t * x) ^ 2 = (z * t) * (z * t) * (x * x) := by
                rw [pow_two]
                calc z * t * x * (z * t * x) = z * t * (x * (z * t)) * x := by group
                  _ = z * t * (z * t * x) * x := by rw [hc]
                  _ = (z * t) * (z * t) * (x * x) := by group
            _ = x ^ 2 := by rw [← pow_two (z * t), ← pow_two x, hζ2, one_mul]
        rw [h7, hx2] at h5
        exact hzt_ne h5
  rcases ht'zt with h | h
  ·
    have huw : u * w' ∈ A.T := by
      refine A.mem_T_of_commute hw'p (le_sup_left.trans le_sup_left)
        (mul_mem (mem_sup_left huT₁) (mem_sup_right (mem_zpowers w'))) ?_
      have : (u * w') * t * (u * w')⁻¹ = t := by
        rw [show (u * w') * t * (u * w')⁻¹ = u * t' * u⁻¹ by rw [ht']; group, h, huz]
      calc u * w' * t = (u * w') * t * (u * w')⁻¹ * (u * w') := by group
        _ = t * (u * w') := by rw [this]
    exact hw'T (by
      have := mul_mem (inv_mem huT₁) (mem_sup_left huw : u * w' ∈ T₁)
      rwa [inv_mul_cancel_left] at this)
  · have hw'T' : w' ∈ A.T := by
      refine A.mem_T_of_commute hw'p (le_sup_left.trans le_sup_left)
        (mem_sup_right (mem_zpowers w')) ?_
      calc w' * t = w' * t * w'⁻¹ * w' := by group
        _ = t * w' := by rw [← ht', h]
    exact hw'T (mem_sup_left hw'T')

end A7Data

end CFSG.ComponentClassification.HSFLit
