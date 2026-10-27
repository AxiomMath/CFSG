module

public import CFSG.GH74.GLS.Stage4.HexCD4Mono

public section

namespace CFSG.GH74.GLS.Stage4.Hex

variable {F K : Type} [Field F] [Field K]

structure D4Funcs (G : GalData F K) (a2 a4 : K → K → F) (ℓ : K → K → K) (A2 A4 : F → K → F)
    (g : F → K → K) : Prop where
  c1 : ∀ s s' t, a2 (s + s') t = a2 s' t + G.trF (ℓ s' t * s) + a2 s t
  c2 : ∀ s s' t, ℓ (s + s') t = ℓ s' t + ℓ s t
  c3 : ∀ s s' t, a4 (s + s') t = a4 s' t + a4 s t
  c4 : ∀ s t t', a2 s (t + t') = a2 s t + a2 s t'
  c5 : ∀ s t t', ℓ s (t + t') = ℓ s t + ℓ s t'
  c6 : ∀ s t t', a4 s (t + t') = a4 s t + (a4 s t' + G.trF (ℓ s t' * t))
  c7 : ∀ x : F, x ≠ 0 → ∀ s t, a2 (G.θ x * s) (G.θ x⁻¹ * t) = x * a2 s t ∧
    ℓ (G.θ x * s) (G.θ x⁻¹ * t) = ℓ s t ∧ a4 (G.θ x * s) (G.θ x⁻¹ * t) = x⁻¹ * a4 s t
  d1 : ∀ c c' s, A2 (c + c') s = A2 c' s + A2 c s
  d2 : ∀ c c' s, g (c + c') s = g c' s + g c s
  d3 : ∀ c c' s, A4 (c + c') s = A4 c' s + c * A2 c' s + A4 c s + G.trF (g c s * (G.θ c' * s))
  d4 : ∀ c s s', A2 c (s + s') = A2 c s + (A2 c s' + G.trF (g c s' * s) + a2 s (G.θ c * s'))
  d5 : ∀ c s s', g c (s + s') = g c s + (g c s' + ℓ s (G.θ c * s'))
  d6 : ∀ c s s', A4 c (s + s') = A4 c s + (A4 c s' + a4 s (G.θ c * s') +
    G.trF ((g c s' + ℓ s (G.θ c * s')) * (G.θ c * s)))
  d7 : ∀ c s t, c * a2 s t = G.trF (ℓ s t * (G.θ c * s)) - G.trF (g c s * t)
  d8 : ∀ x : F, x ≠ 0 → ∀ c s, A2 ((x ^ 2)⁻¹ * c) (G.θ x * s) = x * A2 c s ∧
    g ((x ^ 2)⁻¹ * c) (G.θ x * s) = g c s ∧ A4 ((x ^ 2)⁻¹ * c) (G.θ x * s) = x⁻¹ * A4 c s

namespace GalData

theorem trF_σ (G : GalData F K) (x : K) : G.trF (G.σ x) = G.trF x := by
  apply G.θ.injective
  rw [G.θ_trF, G.θ_trF, G.σ3]
  ring

theorem trF_θ (G : GalData F K) (c : F) : G.trF (G.θ c) = 3 * c := by
  have h := G.trF_smul c 1
  rw [mul_one] at h
  have h1 : G.trF 1 = 3 := by
    apply G.θ.injective
    have h3 : G.θ (3 : F) = 3 := map_ofNat G.θ 3
    rw [G.θ_trF, h3]
    simp only [map_one]
    norm_num
  rw [h, h1]
  ring

end GalData

section Funcs

variable (G : GalData F K) {a2 a4 : K → K → F} {ℓ : K → K → K} {A2 A4 : F → K → F} {g : F → K → K}
  (H : D4Funcs G a2 a4 ℓ A2 A4 g)

include H in
theorem D4Funcs.ℓ_zero (t : K) : ℓ 0 t = 0 := by
  have := H.c2 0 0 t
  rw [add_zero] at this
  exact (add_eq_left.1 this.symm)

include H in
theorem D4Funcs.g_eq (c : F) (s : K) : g c s = G.θ c * g 1 s := by
  apply G.eq_of_trF_eq
  intro t
  have e1 := H.d7 c s t
  have e2 := H.d7 1 s t
  simp only [map_one, one_mul] at e2
  have h1 : G.trF (ℓ s t * (G.θ c * s)) = c * G.trF (ℓ s t * s) := by
    rw [show ℓ s t * (G.θ c * s) = G.θ c * (ℓ s t * s) by ring, G.trF_smul]
  have h3 : G.trF (G.θ c * g 1 s * t) = c * G.trF (g 1 s * t) := by
    rw [show G.θ c * g 1 s * t = G.θ c * (g 1 s * t) by ring, G.trF_smul]
  rw [h3]
  rw [h1] at e1
  linear_combination e1 - c * e2

include H in
theorem D4Funcs.g_one_zero : g 1 0 = 0 := by
  have h := H.d5 1 0 0
  simp only [add_zero, H.ℓ_zero, mul_zero] at h
  exact add_eq_left.1 h.symm

include H in
theorem D4Funcs.Q_add (s s' : K) : g 1 (s + s') = g 1 s + g 1 s' + ℓ s s' := by
  have := H.d5 1 s s'
  simp only [map_one, one_mul] at this
  rw [this]; ring

include H in
theorem D4Funcs.ℓ_hom2 (c : F) (s t : K) : ℓ s (G.θ c * t) = G.θ c * ℓ s t := by
  have h1 := H.d5 c s t
  rw [H.g_eq G c (s + t), H.g_eq G c s, H.g_eq G c t, H.Q_add G s t] at h1
  linear_combination -h1

include H in
theorem D4Funcs.ℓ_hom1 (c : F) (s t : K) : ℓ (G.θ c * s) t = G.θ c * ℓ s t := by
  by_cases hc : c = 0
  · subst hc
    rw [map_zero, zero_mul, zero_mul, H.ℓ_zero]
  · have h := (H.c7 c hc s (G.θ c * t)).2.1
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul] at h
    rw [h, H.ℓ_hom2 G c s t]

include H in
theorem D4Funcs.Q_hom (x : F) (s : K) : g 1 (G.θ x * s) = G.θ x ^ 2 * g 1 s := by
  by_cases hx : x = 0
  · subst hx
    rw [map_zero, zero_mul, zero_pow two_ne_zero, zero_mul]
    exact H.g_one_zero
  · have h := (H.d8 x hx 1 s).2.1
    rw [H.g_eq G ((x ^ 2)⁻¹ * 1) (G.θ x * s)] at h
    have hx' : G.θ x ≠ 0 := (map_ne_zero G.θ).2 hx
    have e : G.θ ((x ^ 2)⁻¹ * 1) = (G.θ x ^ 2)⁻¹ := by rw [mul_one, map_inv₀, map_pow]
    rw [e] at h
    calc g 1 (G.θ x * s) = G.θ x ^ 2 * ((G.θ x ^ 2)⁻¹ * g 1 (G.θ x * s)) := by
          rw [mul_inv_cancel_left₀ (pow_ne_zero 2 hx')]
      _ = _ := by rw [h]

include H in
theorem D4Funcs.ℓ_sym (s s' t : K) : G.trF (ℓ s' t * s) = G.trF (ℓ s t * s') := by
  have h1 := H.c1 s s' t
  have h2 := H.c1 s' s t
  rw [add_comm s' s] at h2
  linear_combination h2 - h1

include H in
theorem d4_Q (h2 : (2 : K) ≠ 0)
    (hcov : ∀ ρ : Kˣ, ∃ χ : Fˣ, ∀ c s, g ((χ : F) * c) ((ρ : K) ^ 2 * s) =
      ((ρ : K) ^ 2)⁻¹ * (G.θ (χ : F))⁻¹ * g c s) :
    ∃ κ : K, ∀ s, g 1 s = κ * (G.σ s * G.σ (G.σ s)) := by
  refine G.quad_monomial h2 (g 1) ℓ (H.Q_add G) (fun s s' t => ?_) (H.c5) (H.ℓ_hom1 G)
    (H.ℓ_hom2 G) (H.Q_hom G) (fun ρ => ?_)
  · rw [H.c2, add_comm]
  · obtain ⟨χ, hχ⟩ := hcov ρ
    refine ⟨χ, fun s => ?_⟩
    have this := hχ 1 s
    rw [H.g_eq G ((χ : F) * 1) ((ρ : K) ^ 2 * s), mul_one] at this
    have hχ0 : G.θ (χ : F) ≠ 0 := (map_ne_zero G.θ).2 χ.ne_zero
    calc g 1 ((ρ : K) ^ 2 * s) = (G.θ χ)⁻¹ * (G.θ χ * g 1 ((ρ : K) ^ 2 * s)) := by
          rw [inv_mul_cancel_left₀ hχ0]
      _ = (G.θ χ)⁻¹ * (((ρ : K) ^ 2)⁻¹ * (G.θ χ)⁻¹ * g 1 s) := by rw [this]
      _ = _ := by ring

end Funcs

end CFSG.GH74.GLS.Stage4.Hex
