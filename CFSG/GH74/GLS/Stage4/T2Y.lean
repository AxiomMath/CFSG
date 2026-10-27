module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage4.RestSetupRank

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup

section Four

variable {G : Type} [Group G] {z u : G}

@[expose] def t2U (z u : G) : Subgroup G := Subgroup.closure {z, u}

theorem t2U_mem (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z) {x : G} :
    x ∈ t2U z u ↔ x = 1 ∨ x = z ∨ x = u ∨ x = z * u := by
  have hz : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    | one => exact Or.inl rfl
    | mul a b _ _ ha hb =>
      have e4 : z * (z * u) = u := by
        calc z * (z * u) = (z * z) * u := by group
          _ = u := by rw [hz2, one_mul]
      have e5 : u * (z * u) = z := by
        calc u * (z * u) = (u * z) * u := by group
          _ = (z * u) * u := by rw [hzu]
          _ = z := by rw [mul_assoc, hu2, mul_one]
      have e6 : z * u * z = u := by
        calc z * u * z = (u * z) * z := by rw [hzu]
          _ = u := by rw [mul_assoc, hz2, mul_one]
      have e7 : z * u * u = z := by
        calc z * u * u = z * (u * u) := by group
          _ = z := by rw [hu2, mul_one]
      have e8 : z * u * (z * u) = 1 := by
        calc z * u * (z * u) = z * (u * z) * u := by group
          _ = z * (z * u) * u := by rw [← hzu]
          _ = (z * z) * (u * u) := by group
          _ = 1 := by rw [hz2, hu2, one_mul]
      have e9 : u * z = z * u := hzu.symm
      rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb <;> rw [ha, hb] <;>
        simp [hz2, hu2, e4, e5, e6, e7, e8, e9]
    | inv a _ ha =>
      have e9 : u * z = z * u := hzu.symm
      rcases ha with ha | ha | ha | ha <;> rw [ha]
      · simp
      · simp [hz]
      · simp [hu]
      · have : (z * u)⁻¹ = z * u := by
          calc (z * u)⁻¹ = u⁻¹ * z⁻¹ := by group
            _ = u * z := by rw [hu, hz]
            _ = z * u := hzu.symm
        simp [this]
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

end Four

section Y

variable {G : Type} [Group G]

theorem t2Y_decomp {C₁ F H : Subgroup G} {z u w₀ : G}
    (hCle : centralizer ({z} : Set G) ≤ C₁ ⊔ F) (hFn : F ≤ normalizer (C₁ : Set G))
    (hFu : ∀ f ∈ F, f * u = u * f)
    (hY1 : ∀ c ∈ C₁, c * u = u * c → c ∈ H ∨ ∃ h ∈ H, c = h * w₀)
    {y : G} (hyz : y * z = z * y) (hyu : y * u = u * y) :
    ∃ k f : G, f ∈ F ∧ (k ∈ H ∨ ∃ h ∈ H, k = h * w₀) ∧ y = k * f := by
  have hy : y ∈ C₁ ⊔ F := hCle (Subgroup.mem_centralizer_singleton_iff.2 hyz)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left C₁ F hFn] at hy
  obtain ⟨c, hc, f, hf, rfl⟩ := hy
  refine ⟨c, f, hf, hY1 c hc ?_, rfl⟩
  have h1 : c * f * u = u * (c * f) := hyu
  have h2 : c * u * f = u * c * f := by
    calc c * u * f = c * (u * f) := by group
      _ = c * (f * u) := by rw [hFu f hf]
      _ = c * f * u := by group
      _ = u * (c * f) := h1
      _ = u * c * f := by group
  exact mul_right_cancel h2

theorem t2Y_F_inter {F H : Subgroup G} {w₀ : G} (hFodd : ∀ f ∈ F, Odd (orderOf f))
    (hFw : ∀ f ∈ F, f * w₀ = w₀ * f) (hw₀2 : w₀ * w₀ = 1)
    (hinv : ∀ h ∈ H, w₀ * h * w₀⁻¹ = h⁻¹) {f : G} (hf : f ∈ F)
    (hfH : f ∈ H ∨ ∃ h ∈ H, f = h * w₀) : f = 1 := by
  have hw₀ : w₀⁻¹ = w₀ := inv_eq_of_mul_eq_one_right hw₀2
  have hff : f * f = 1 := by
    rcases hfH with h | ⟨h, hh, rfl⟩
    · have h1 := hinv f h
      rw [hw₀] at h1
      have h2 : w₀ * f * w₀ = f := by
        calc w₀ * f * w₀ = f * w₀ * w₀ := by rw [← hFw f hf]
          _ = f := by rw [mul_assoc, hw₀2, mul_one]
      rw [h2] at h1
      calc f * f = f * f⁻¹ := by rw [← h1]
        _ = 1 := by group
    · have h1 := hinv h hh
      rw [hw₀] at h1
      calc h * w₀ * (h * w₀) = h * (w₀ * h * w₀) := by group
        _ = h * h⁻¹ := by rw [h1]
        _ = 1 := by group
  have hdvd : orderOf f ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hff)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · exact orderOf_eq_one_iff.1 h1
  · exact absurd (hFodd f hf) (by rw [h2]; decide)

theorem t2Y_inv {F H : Subgroup G} {z u w₀ : G}
    (hdec : ∀ y : G, y * z = z * y → y * u = u * y →
      ∃ k f : G, f ∈ F ∧ (k ∈ H ∨ ∃ h ∈ H, k = h * w₀) ∧ y = k * f)
    (hFodd : ∀ f ∈ F, Odd (orderOf f)) (hFw : ∀ f ∈ F, f * w₀ = w₀ * f)
    (hFH : ∀ f ∈ F, ∀ h ∈ H, f * h * f⁻¹ ∈ H) (hw₀2 : w₀ * w₀ = 1)
    (hinv : ∀ h ∈ H, w₀ * h * w₀⁻¹ = h⁻¹)
    (hΩ : ∀ x ∈ H, x * x = 1 → x = 1 ∨ x = z ∨ x = u ∨ x = z * u)
    {y : G} (hyz : y * z = z * y) (hyu : y * u = u * y) (hy2 : y * y = 1)
    (hyU : ¬ (y = 1 ∨ y = z ∨ y = u ∨ y = z * u)) : ∃ h ∈ H, y = h * w₀ := by
  have hw₀ : w₀⁻¹ = w₀ := inv_eq_of_mul_eq_one_right hw₀2
  obtain ⟨k, f, hf, hk, rfl⟩ := hdec _ hyz hyu
  have hf2 : f * f ∈ F := F.mul_mem hf hf
  rcases hk with hk | ⟨h, hh, rfl⟩
  ·
    have hk' : f * k * f⁻¹ ∈ H := hFH f hf k hk
    have hf2H : f * f ∈ H := by
      have : f * f = (k * (f * k * f⁻¹))⁻¹ := by
        have h1 : k * f * (k * f) = 1 := hy2
        have h2 : k * (f * k * f⁻¹) * (f * f) = 1 := by
          calc k * (f * k * f⁻¹) * (f * f) = k * f * (k * f) := by group
            _ = 1 := h1
        exact eq_inv_of_mul_eq_one_right h2
      rw [this]
      exact H.inv_mem (H.mul_mem hk hk')
    have hf1 : f * f = 1 := t2Y_F_inter hFodd hFw hw₀2 hinv hf2 (Or.inl hf2H)
    have hf1' : f = 1 := by
      have hdvd : orderOf f ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hf1)
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
      · exact orderOf_eq_one_iff.1 h1
      · exact absurd (hFodd f hf) (by rw [h2]; decide)
    subst hf1'
    have hkk : k * k = 1 := by simpa using hy2
    exact absurd (by simpa using hΩ k hk hkk) hyU
  ·
    have hh' : f * h * f⁻¹ ∈ H := hFH f hf h hh
    have hf2H : f * f ∈ H := by
      have h1 : h * w₀ * f * (h * w₀ * f) = 1 := hy2
      have hw₀h := hinv (f * h * f⁻¹) hh'
      have hfw := hFw f hf
      have h2 : (h * w₀ * f) * (h * w₀ * f) = h * (w₀ * (f * h * f⁻¹) * w₀⁻¹) * (f * f) := by
        calc (h * w₀ * f) * (h * w₀ * f) = h * w₀ * (f * h * f⁻¹) * (f * w₀) * f := by group
          _ = h * w₀ * (f * h * f⁻¹) * (w₀ * f) * f := by rw [hfw]
          _ = h * (w₀ * (f * h * f⁻¹) * w₀⁻¹) * (w₀ * w₀) * (f * f) := by group
          _ = h * (w₀ * (f * h * f⁻¹) * w₀⁻¹) * (f * f) := by rw [hw₀2, mul_one]
      rw [h2, hw₀h] at h1
      have : f * f = (h * (f * h * f⁻¹)⁻¹)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this]
      exact H.inv_mem (H.mul_mem hh (H.inv_mem hh'))
    have hf1 : f * f = 1 := t2Y_F_inter hFodd hFw hw₀2 hinv hf2 (Or.inl hf2H)
    have hf1' : f = 1 := by
      have hdvd : orderOf f ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hf1)
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
      · exact orderOf_eq_one_iff.1 h1
      · exact absurd (hFodd f hf) (by rw [h2]; decide)
    subst hf1'
    exact ⟨h, hh, by simp⟩

theorem t2Y_key {H : Subgroup G} {z u w₀ t : G}
    (hInv : ∀ y : G, y * z = z * y → y * u = u * y → y * y = 1 →
      ¬ (y = 1 ∨ y = z ∨ y = u ∨ y = z * u) → ∃ h ∈ H, y = h * w₀)
    (hHc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hzH : z ∈ H) (huH : u ∈ H)
    (hw₀2 : w₀ * w₀ = 1) (hw₀H : w₀ ∉ H) (hw₀z : w₀ * z = z * w₀) (hw₀u : w₀ * u = u * w₀)
    (hinv : ∀ h ∈ H, w₀ * h * w₀⁻¹ = h⁻¹)
    (htU' : ∀ v, (v = 1 ∨ v = z ∨ v = u ∨ v = z * u) →
      (t⁻¹ * v * t = 1 ∨ t⁻¹ * v * t = z ∨ t⁻¹ * v * t = u ∨ t⁻¹ * v * t = z * u)) :
    ∀ h ∈ H, ∃ h' ∈ H, t * (h * w₀) * t⁻¹ = h' * w₀ := by
  have hw₀ : w₀⁻¹ = w₀ := inv_eq_of_mul_eq_one_right hw₀2
  have hUH : ∀ v, (v = 1 ∨ v = z ∨ v = u ∨ v = z * u) → v ∈ H := by
    rintro v (rfl | rfl | rfl | rfl)
    · exact H.one_mem
    · exact hzH
    · exact huH
    · exact H.mul_mem hzH huH
  intro h hh
  have hxv : ∀ v, (v = 1 ∨ v = z ∨ v = u ∨ v = z * u) → (h * w₀) * v = v * (h * w₀) := by
    intro v hv
    have hvH := hUH v hv
    have hw₀v : w₀ * v = v * w₀ := by
      rcases hv with rfl | rfl | rfl | rfl
      · simp
      · exact hw₀z
      · exact hw₀u
      · calc w₀ * (z * u) = (w₀ * z) * u := by group
          _ = z * (w₀ * u) := by rw [hw₀z]; group
          _ = z * (u * w₀) := by rw [hw₀u]
          _ = (z * u) * w₀ := by group
    calc h * w₀ * v = h * (w₀ * v) := by group
      _ = h * (v * w₀) := by rw [hw₀v]
      _ = (h * v) * w₀ := by group
      _ = (v * h) * w₀ := by rw [hHc h hh v hvH]
      _ = v * (h * w₀) := by group
  set y := t * (h * w₀) * t⁻¹ with hy
  have hyv : ∀ v, (v = 1 ∨ v = z ∨ v = u ∨ v = z * u) → y * v = v * y := by
    intro v hv
    have hv' := htU' v hv
    have hcomm : (h * w₀) * (t⁻¹ * v * t) = (t⁻¹ * v * t) * (h * w₀) := hxv _ hv'
    calc y * v = t * ((h * w₀) * (t⁻¹ * v * t)) * t⁻¹ := by rw [hy]; group
      _ = t * ((t⁻¹ * v * t) * (h * w₀)) * t⁻¹ := by rw [hcomm]
      _ = v * y := by rw [hy]; group
  have hy2 : y * y = 1 := by
    have h1 : (h * w₀) * (h * w₀) = 1 := by
      have h2 := hinv h hh
      rw [hw₀] at h2
      calc h * w₀ * (h * w₀) = h * (w₀ * h * w₀) := by group
        _ = h * h⁻¹ := by rw [h2]
        _ = 1 := by group
    calc y * y = t * ((h * w₀) * (h * w₀)) * t⁻¹ := by rw [hy]; group
      _ = 1 := by rw [h1]; group
  have hyU : ¬ (y = 1 ∨ y = z ∨ y = u ∨ y = z * u) := by
    intro hyU
    have hx := htU' y hyU
    have : t⁻¹ * y * t = h * w₀ := by rw [hy]; group
    rw [this] at hx
    have hxH : h * w₀ ∈ H := hUH _ hx
    exact hw₀H (by simpa using H.mul_mem (H.inv_mem hh) hxH)
  exact hInv y (hyv z (Or.inr (Or.inl rfl))) (hyv u (Or.inr (Or.inr (Or.inl rfl)))) hy2 hyU

theorem t2Y_normH {H : Subgroup G} {z u w₀ t : G}
    (hInv : ∀ y : G, y * z = z * y → y * u = u * y → y * y = 1 →
      ¬ (y = 1 ∨ y = z ∨ y = u ∨ y = z * u) → ∃ h ∈ H, y = h * w₀)
    (hHc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hzH : z ∈ H) (huH : u ∈ H)
    (hw₀2 : w₀ * w₀ = 1) (hw₀H : w₀ ∉ H) (hw₀z : w₀ * z = z * w₀) (hw₀u : w₀ * u = u * w₀)
    (hinv : ∀ h ∈ H, w₀ * h * w₀⁻¹ = h⁻¹)
    (htU' : ∀ v, (v = 1 ∨ v = z ∨ v = u ∨ v = z * u) →
      (t⁻¹ * v * t = 1 ∨ t⁻¹ * v * t = z ∨ t⁻¹ * v * t = u ∨ t⁻¹ * v * t = z * u)) :
    ∀ h ∈ H, t * h * t⁻¹ ∈ H := by
  have hw₀ : w₀⁻¹ = w₀ := inv_eq_of_mul_eq_one_right hw₀2
  have key := t2Y_key hInv hHc hzH huH hw₀2 hw₀H hw₀z hw₀u hinv htU'
  intro h hh
  obtain ⟨h₁, hh₁, e₁⟩ := key h hh
  obtain ⟨h₂, hh₂, e₂⟩ := key 1 H.one_mem
  rw [one_mul] at e₂
  have : t * h * t⁻¹ = (t * (h * w₀) * t⁻¹) * (t * w₀ * t⁻¹) := by
    calc t * h * t⁻¹ = t * (h * w₀ * w₀) * t⁻¹ := by rw [mul_assoc h w₀ w₀, hw₀2, mul_one]
      _ = (t * (h * w₀) * t⁻¹) * (t * w₀ * t⁻¹) := by group
  rw [this, e₁, e₂]
  have h3 := hinv h₂ hh₂
  rw [hw₀] at h3
  have h4 : h₁ * w₀ * (h₂ * w₀) = h₁ * h₂⁻¹ := by
    calc h₁ * w₀ * (h₂ * w₀) = h₁ * (w₀ * h₂ * w₀) := by group
      _ = h₁ * h₂⁻¹ := by rw [h3]
  rw [h4]
  exact H.mul_mem hh₁ (H.inv_mem hh₂)

end Y

end CFSG.GH74.GLS.Stage4.Rest
