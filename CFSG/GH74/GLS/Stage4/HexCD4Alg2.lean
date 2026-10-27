module

public import CFSG.GH74.GLS.Stage4.HexCD4Alg1

public section

namespace CFSG.GH74.GLS.Stage4.Hex

variable {F K : Type} [Field F] [Field K]

namespace GalData

variable (G : GalData F K)

@[expose] def sharp (s : K) : K := G.σ s * G.σ (G.σ s)

@[expose] def cross (s t : K) : K := G.σ s * G.σ (G.σ t) + G.σ (G.σ s) * G.σ t

theorem sharp_add (s t : K) : G.sharp (s + t) = G.sharp s + G.sharp t + G.cross s t := by
  simp only [sharp, cross, map_add]; ring

theorem sharp_smul (x : F) (s : K) : G.sharp (G.θ x * s) = G.θ x ^ 2 * G.sharp s := by
  simp only [sharp, map_mul, G.σ_θ]; ring

theorem trF_σ_eq {x y : K} (h : G.σ x = y) : G.trF x = G.trF y := by
  rw [← h, G.trF_σ]

theorem trF_σσ_eq {x y : K} (h : G.σ (G.σ x) = y) : G.trF x = G.trF y := by
  rw [← h, G.trF_σ, G.trF_σ]

theorem trF_cross_self (s t : K) : G.trF (G.cross s t * s) = 2 * G.trF (G.sharp s * t) := by
  have h1 : G.trF (G.σ s * G.σ (G.σ t) * s) = G.trF (G.sharp s * t) :=
    G.trF_σ_eq (by simp only [sharp, map_mul, G.σ3]; ring)
  have h2 : G.trF (G.σ (G.σ s) * G.σ t * s) = G.trF (G.sharp s * t) :=
    G.trF_σσ_eq (by simp only [sharp, map_mul, G.σ3]; ring)
  rw [show G.cross s t * s = G.σ s * G.σ (G.σ t) * s + G.σ (G.σ s) * G.σ t * s by
    simp only [cross]; ring, G.trF_add, h1, h2]
  ring

theorem trF_cross_swap (s t t' : K) : G.trF (G.cross s t' * t) = G.trF (s * G.cross t t') := by
  have h1 : G.trF (G.σ s * G.σ (G.σ t') * t) = G.trF (s * (G.σ t' * G.σ (G.σ t))) :=
    G.trF_σσ_eq (by simp only [map_mul, G.σ3]; ring)
  have h2 : G.trF (G.σ (G.σ s) * G.σ t' * t) = G.trF (s * (G.σ (G.σ t') * G.σ t)) :=
    G.trF_σ_eq (by simp only [map_mul, G.σ3]; ring)
  rw [show G.cross s t' * t = G.σ s * G.σ (G.σ t') * t + G.σ (G.σ s) * G.σ t' * t by
    simp only [cross]; ring, G.trF_add, h1, h2,
    show s * G.cross t t' = s * (G.σ t' * G.σ (G.σ t)) + s * (G.σ (G.σ t') * G.σ t) by
      simp only [cross]; ring, G.trF_add]

theorem tr_gl (c k : F) (s s' : K) :
    G.trF ((G.θ c * (G.θ k * G.sharp s') + G.θ c * (G.θ k * G.cross s s')) * (G.θ c * s)) =
      c * c * k * (G.trF (G.sharp s' * s) + 2 * G.trF (G.sharp s * s')) := by
  have e : (G.θ c * (G.θ k * G.sharp s') + G.θ c * (G.θ k * G.cross s s')) * (G.θ c * s) =
      G.θ (c * c * k) * (G.sharp s' * s + G.cross s s' * s) := by
    simp only [map_mul]; ring
  rw [e, G.trF_smul, G.trF_add, G.trF_cross_self]

theorem trF_s_sharp_smul (c : F) (s s' : K) :
    G.trF (s * G.sharp (G.θ c * s')) = c * c * G.trF (G.sharp s' * s) := by
  rw [G.sharp_smul, show s * (G.θ c ^ 2 * G.sharp s') = G.θ (c * c) * (G.sharp s' * s) by
    simp only [map_mul]; ring, G.trF_smul]

end GalData

section Funcs

variable (G : GalData F K) {a2 a4 : K → K → F} {ℓ : K → K → K} {A2 A4 : F → K → F} {g : F → K → K}
  (H : D4Funcs G a2 a4 ℓ A2 A4 g)

include H in
theorem D4Funcs.ℓ_eq {κ : K} (hκ : ∀ s, g 1 s = κ * G.sharp s) (s t : K) :
    ℓ s t = κ * G.cross s t := by
  have := H.Q_add G s t
  rw [hκ, hκ, hκ, G.sharp_add] at this
  linear_combination -this

include H in
theorem d4_kappa {κ : K} (hκ : ∀ s, g 1 s = κ * G.sharp s) : G.σ κ = κ := by
  have hℓ := H.ℓ_eq G hκ
  have key : ∀ s s' : K, G.trF ((G.σ (G.σ κ) * G.σ (G.σ s) + G.σ κ * G.σ s) * s') =
      G.trF ((κ * G.σ s + κ * G.σ (G.σ s)) * s') := by
    intro s s'
    have h := H.ℓ_sym G s s' 1
    rw [hℓ, hℓ] at h
    simp only [GalData.cross, map_one, mul_one] at h
    have e1 : G.trF (κ * G.σ s' * s) = G.trF (G.σ (G.σ κ) * G.σ (G.σ s) * s') :=
      G.trF_σσ_eq (by simp only [map_mul, G.σ3]; ring)
    have e2 : G.trF (κ * G.σ (G.σ s') * s) = G.trF (G.σ κ * G.σ s * s') :=
      G.trF_σ_eq (by simp only [map_mul, G.σ3]; ring)
    calc G.trF ((G.σ (G.σ κ) * G.σ (G.σ s) + G.σ κ * G.σ s) * s')
        = G.trF (G.σ (G.σ κ) * G.σ (G.σ s) * s') + G.trF (G.σ κ * G.σ s * s') := by
          rw [← G.trF_add]; congr 1; ring
      _ = G.trF (κ * G.σ s' * s) + G.trF (κ * G.σ (G.σ s') * s) := by rw [e1, e2]
      _ = G.trF (κ * (G.σ s' + G.σ (G.σ s')) * s) := by rw [← G.trF_add]; congr 1; ring
      _ = G.trF (κ * (G.σ s + G.σ (G.σ s)) * s') := h
      _ = _ := by congr 1; ring
  obtain ⟨-, h1, -⟩ := G.indep3 0 (G.σ κ - κ) (G.σ (G.σ κ) - κ) (fun s => by
    have := G.eq_of_trF_eq (key s)
    linear_combination this)
  exact sub_eq_zero.1 h1

include H in
theorem d4_a2 {k : F} (hκ : ∀ s, g 1 s = G.θ k * G.sharp s) (s t : K) :
    a2 s t = k * G.trF (G.sharp s * t) := by
  have h := H.d7 1 s t
  simp only [map_one, one_mul] at h
  rw [H.ℓ_eq G hκ, hκ] at h
  rw [h, show G.θ k * G.cross s t * s = G.θ k * (G.cross s t * s) by ring, G.trF_smul,
    show G.θ k * G.sharp s * t = G.θ k * (G.sharp s * t) by ring, G.trF_smul, G.trF_cross_self]
  ring

include H in
theorem d4_a4 (h2 : (2 : F) ≠ 0) {k : F} (hκ : ∀ s, g 1 s = G.θ k * G.sharp s) (s t : K) :
    a4 s t = k * G.trF (s * G.sharp t) := by
  have hℓ := H.ℓ_eq G hκ
  have hk : ∀ s t' t : K, G.trF (G.θ k * G.cross s t' * t) = k * G.trF (s * G.cross t t') := by
    intro s t' t
    rw [mul_assoc, G.trF_smul, G.trF_cross_swap]
  set δ : K → K → F := fun s t => a4 s t - k * G.trF (s * G.sharp t) with hδ
  have δ2 : ∀ s t t', δ s (t + t') = δ s t + δ s t' := by
    intro s t t'
    simp only [hδ]
    rw [H.c6, hℓ s t', hk, G.sharp_add, mul_add, mul_add, G.trF_add, G.trF_add]
    ring
  have δ3 : ∀ x : F, x ≠ 0 → ∀ s t, δ (G.θ x * s) (G.θ x⁻¹ * t) = x⁻¹ * δ s t := by
    intro x hx s t
    simp only [hδ]
    have hxx : G.θ x * G.θ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hx, map_one]
    have e : G.θ x * s * (G.θ x⁻¹ ^ 2 * G.sharp t) = G.θ x⁻¹ * (s * G.sharp t) := by
      linear_combination (G.θ x⁻¹ * s * G.sharp t) * hxx
    rw [(H.c7 x hx s t).2.2, G.sharp_smul, e, G.trF_smul]
    ring
  have δ4 : ∀ c s s', δ s (G.θ c * s') = δ s' (G.θ c * s) := by
    intro c s s'
    have h := H.d6 c s s'
    have h' := H.d6 c s' s
    rw [add_comm s' s] at h'
    have T1 : G.trF ((g c s' + ℓ s (G.θ c * s')) * (G.θ c * s)) =
        c * c * k * (G.trF (G.sharp s' * s) + 2 * G.trF (G.sharp s * s')) := by
      rw [H.g_eq G c s', hκ, H.ℓ_hom2 G c, hℓ]
      exact G.tr_gl c k s s'
    have T2 : G.trF ((g c s + ℓ s' (G.θ c * s)) * (G.θ c * s')) =
        c * c * k * (G.trF (G.sharp s * s') + 2 * G.trF (G.sharp s' * s)) := by
      rw [H.g_eq G c s, hκ, H.ℓ_hom2 G c, hℓ]
      exact G.tr_gl c k s' s
    have M1 := G.trF_s_sharp_smul c s s'
    have M2 := G.trF_s_sharp_smul c s' s
    have hh : a4 s (G.θ c * s') +
        c * c * k * (G.trF (G.sharp s' * s) + 2 * G.trF (G.sharp s * s')) =
        a4 s' (G.θ c * s) + c * c * k * (G.trF (G.sharp s * s') + 2 * G.trF (G.sharp s' * s)) := by
      rw [← T1, ← T2]
      linear_combination h' - h
    simp only [hδ]
    rw [M1, M2]
    linear_combination hh
  have δsym : ∀ s s', δ s s' = δ s' s := by
    intro s s'
    have := δ4 1 s s'
    simpa using this
  have transfer : ∀ c s s', δ (G.θ c * s) s' = δ s (G.θ c * s') := fun c s s' =>
    (δsym _ _).trans (δ4 c s s').symm
  have hδ0 : ∀ s t, δ s t = 0 := by
    intro s t
    have hx : ((-1 : F)) ≠ 0 := neg_ne_zero.2 one_ne_zero
    have h1 := δ3 (-1) hx s t
    have hxx : G.θ (-1 : F) * G.θ (-1 : F)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hx, map_one]
    have hmove : δ (G.θ (-1) * s) (G.θ (-1 : F)⁻¹ * t) = δ s t := by
      rw [transfer, ← mul_assoc, hxx, one_mul]
    rw [hmove] at h1
    have h3 : δ s t = -δ s t := by
      have e : ((-1 : F))⁻¹ = -1 := by norm_num
      rw [e] at h1; linear_combination h1
    have : (2 : F) * δ s t = 0 := by linear_combination h3
    exact (mul_eq_zero.1 this).resolve_left h2
  have := hδ0 s t
  simp only [hδ] at this
  linear_combination this

end Funcs

end CFSG.GH74.GLS.Stage4.Hex
