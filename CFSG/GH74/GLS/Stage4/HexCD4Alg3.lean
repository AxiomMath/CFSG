module

public import CFSG.GH74.GLS.Stage4.HexCD4Alg2

public section

namespace CFSG.GH74.GLS.Stage4.Hex

variable {F K : Type} [Field F] [Field K]

namespace GalData

variable (G : GalData F K)

@[expose] def norm' (s : K) : K := s * G.σ s * G.σ (G.σ s)

theorem σ_norm' (s : K) : G.σ (G.norm' s) = G.norm' s := by
  simp only [norm', map_mul, G.σ3]; ring

theorem exists_Nm (s : K) : ∃ n : F, G.θ n = G.norm' s := G.fixed_eq (G.σ_norm' s)

noncomputable def Nm (s : K) : F := Classical.choose (G.exists_Nm s)

theorem θ_Nm (s : K) : G.θ (G.Nm s) = G.norm' s := Classical.choose_spec (G.exists_Nm s)

theorem Nm_add (s s' : K) :
    G.Nm (s + s') = G.Nm s + G.Nm s' + (G.trF (G.sharp s * s') + G.trF (G.sharp s' * s)) := by
  apply G.θ.injective
  simp only [map_add, G.θ_Nm, G.θ_trF]
  simp only [norm', sharp, map_add, map_mul, G.σ3]
  ring

theorem Nm_smul (x : F) (s : K) : G.Nm (G.θ x * s) = x ^ 3 * G.Nm s := by
  apply G.θ.injective
  rw [G.θ_Nm, map_mul, map_pow, G.θ_Nm]
  simp only [norm', map_mul, G.σ_θ]; ring

theorem Nm_neg (s : K) : G.Nm (-s) = -G.Nm s := by
  apply G.θ.injective
  rw [G.θ_Nm, map_neg, G.θ_Nm]
  simp only [norm', map_neg]; ring

theorem trF_sharp_self (s : K) : G.trF (G.sharp s * s) = 3 * G.Nm s := by
  have h : G.sharp s * s = G.θ (G.Nm s) := by
    rw [G.θ_Nm]; simp only [sharp, norm']; ring
  rw [h, G.trF_θ]

theorem exists_polar_ne : ∃ s s' : K, G.trF (G.sharp s * s') + G.trF (G.sharp s' * s) ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have hadd : ∀ s s', G.norm' (s + s') = G.norm' s + G.norm' s' := by
    intro s s'
    have h := G.Nm_add s s'
    rw [hcon s s', add_zero] at h
    rw [← G.θ_Nm, ← G.θ_Nm, ← G.θ_Nm, h, map_add]
  let N : K →+* K :=
    { toFun := G.norm'
      map_one' := by simp only [norm', map_one, mul_one]
      map_mul' := fun s t => by simp only [norm', map_mul]; ring
      map_zero' := by simp only [norm', map_zero, mul_zero]
      map_add' := hadd }
  have hσ : ∀ s, G.σ s = s := fun s => N.injective (by
    show G.norm' (G.σ s) = G.norm' s
    simp only [norm', G.σ3]; ring)
  have hbij : Function.Bijective G.θ := ⟨G.θ.injective, fun x => G.fixed_eq (hσ x)⟩
  have hcard := Nat.card_eq_of_bijective _ hbij
  rw [G.hF, G.hK] at hcard
  have hq := G.hq
  have := Nat.pow_lt_pow_right (show 1 < G.q by omega) (show 1 < 3 by norm_num)
  rw [pow_one] at this
  omega

end GalData

section Funcs

variable (G : GalData F K) {a2 a4 : K → K → F} {ℓ : K → K → K} {A2 A4 : F → K → F} {g : F → K → K}
  (H : D4Funcs G a2 a4 ℓ A2 A4 g)

include H in
theorem D4Funcs.A2_eq (c : F) (s : K) : A2 c s = c * A2 1 s := by
  have h := H.d3 c 1 s
  have h' := H.d3 1 c s
  rw [add_comm 1 c] at h'
  have e1 : G.trF (g c s * (G.θ 1 * s)) = c * G.trF (g 1 s * s) := by
    rw [H.g_eq G c s, map_one, one_mul, show G.θ c * g 1 s * s = G.θ c * (g 1 s * s) by ring,
      G.trF_smul]
  have e2 : G.trF (g 1 s * (G.θ c * s)) = c * G.trF (g 1 s * s) := by
    rw [show g 1 s * (G.θ c * s) = G.θ c * (g 1 s * s) by ring, G.trF_smul]
  rw [e1] at h
  rw [e2] at h'
  linear_combination h - h'

include H in
theorem d4_A2 (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {k : F}
    (hκ : ∀ s, g 1 s = G.θ k * G.sharp s) (ha2 : ∀ s t, a2 s t = k * G.trF (G.sharp s * t)) :
    ∀ c s, A2 c s = c * (k * G.Nm s) := by
  have hadd : ∀ s s', A2 1 (s + s') = A2 1 s + A2 1 s' +
      k * (G.trF (G.sharp s * s') + G.trF (G.sharp s' * s)) := by
    intro s s'
    have h := H.d4 1 s s'
    simp only [map_one, one_mul] at h
    rw [hκ, ha2, show G.θ k * G.sharp s' * s = G.θ k * (G.sharp s' * s) by ring, G.trF_smul] at h
    rw [h]; ring
  have hhom : ∀ x : F, x ≠ 0 → ∀ s, A2 1 (G.θ x * s) = x ^ 3 * A2 1 s := by
    intro x hx s
    have h := (H.d8 x hx 1 s).1
    rw [H.A2_eq G ((x ^ 2)⁻¹ * 1) (G.θ x * s)] at h
    calc A2 1 (G.θ x * s) = x ^ 2 * ((x ^ 2)⁻¹ * 1 * A2 1 (G.θ x * s)) := by field_simp
      _ = x ^ 2 * (x * A2 1 s) := by rw [h]
      _ = x ^ 3 * A2 1 s := by ring
  have hε : ∀ s, A2 1 s - k * G.Nm s = 0 := by
    intro s
    have e1 : A2 1 (s + s) - k * G.Nm (s + s) =
        (A2 1 s - k * G.Nm s) + (A2 1 s - k * G.Nm s) := by
      rw [hadd, G.Nm_add]; ring
    have e2 : A2 1 (s + s) - k * G.Nm (s + s) = 8 * (A2 1 s - k * G.Nm s) := by
      have h2' : G.θ (2 : F) = 2 := map_ofNat G.θ 2
      have : s + s = G.θ 2 * s := by rw [h2']; ring
      rw [this, hhom 2 h2, G.Nm_smul]; ring
    have h6 : (6 : F) * (A2 1 s - k * G.Nm s) = 0 := by linear_combination e1 - e2
    have h6ne : (6 : F) ≠ 0 := by
      have : (6 : F) = 2 * 3 := by norm_num
      rw [this]; exact mul_ne_zero h2 h3
    exact (mul_eq_zero.1 h6).resolve_left h6ne
  intro c s
  rw [H.A2_eq G c s, show A2 1 s = k * G.Nm s by linear_combination hε s]

include H in
theorem d4_A4 (h2 : (2 : F) ≠ 0) {k : F} (hκ : ∀ s, g 1 s = G.θ k * G.sharp s)
    (ha4 : ∀ s t, a4 s t = k * G.trF (s * G.sharp t))
    (hA2 : ∀ c s, A2 c s = c * (k * G.Nm s)) {φ₂ : F}
    (hslot : ∀ s, φ₂ * A2 1 s + a4 (-s) s = A4 (-1) (-s)) :
    ∀ c s, A4 c s = 2 * k * c ^ 2 * G.Nm s := by
  set B : F → K → F := fun c s => A4 c s - 2 * k * c ^ 2 * G.Nm s with hB
  have hBc : ∀ c c' s, B (c + c') s = B c' s + B c s := by
    intro c c' s
    have h := H.d3 c c' s
    have e : G.trF (g c s * (G.θ c' * s)) = c * c' * k * (3 * G.Nm s) := by
      rw [H.g_eq G c s, hκ, show G.θ c * (G.θ k * G.sharp s) * (G.θ c' * s) =
        G.θ (c * c' * k) * (G.sharp s * s) by simp only [map_mul]; ring, G.trF_smul,
        G.trF_sharp_self]
    rw [e, hA2 c' s] at h
    simp only [hB]
    rw [h]; ring
  have hBs : ∀ c s s', B c (s + s') = B c s + B c s' := by
    intro c s s'
    have h := H.d6 c s s'
    have T1 : G.trF ((g c s' + ℓ s (G.θ c * s')) * (G.θ c * s)) =
        c * c * k * (G.trF (G.sharp s' * s) + 2 * G.trF (G.sharp s * s')) := by
      rw [H.g_eq G c s', hκ, H.ℓ_hom2 G c, H.ℓ_eq G hκ]
      exact G.tr_gl c k s s'
    rw [T1, ha4, G.trF_s_sharp_smul c s s'] at h
    simp only [hB]
    rw [h, G.Nm_add]; ring
  have hBτ : ∀ x : F, x ≠ 0 → ∀ c s, B ((x ^ 2)⁻¹ * c) (G.θ x * s) = x⁻¹ * B c s := by
    intro x hx c s
    have h := (H.d8 x hx c s).2.2
    simp only [hB]
    rw [h, G.Nm_smul]
    field_simp
  have hB0 : ∀ s, B 0 s = 0 := by
    intro s; have := hBc 0 0 s; rw [add_zero] at this; linear_combination -this
  have hBneg : ∀ c s, B (-c) s = - B c s := by
    intro c s; have := hBc (-c) c s; rw [neg_add_cancel, hB0] at this; linear_combination -this
  have hBs0 : ∀ c, B c 0 = 0 := by
    intro c; have := hBs c 0 0; rw [add_zero] at this; linear_combination -this
  have hBsneg : ∀ c s, B c (-s) = - B c s := by
    intro c s; have := hBs c s (-s); rw [add_neg_cancel, hBs0] at this; linear_combination -this
  have hB1 : ∀ s, B 1 s = (φ₂ - 1) * k * G.Nm s := by
    intro s
    have h := hslot s
    have e : G.trF (-s * G.sharp s) = -(3 * G.Nm s) := by
      rw [show -s * G.sharp s = -(G.sharp s * s) by ring, G.trF_neg, G.trF_sharp_self]
    rw [hA2 1 s, ha4 (-s) s, e] at h
    have hb : B (-1) (-s) = B 1 s := by rw [hBneg, hBsneg]; ring
    have hA : A4 (-1) (-s) = B (-1) (-s) + 2 * k * (-1) ^ 2 * G.Nm (-s) := by simp only [hB]; ring
    rw [hA, hb, G.Nm_neg] at h
    linear_combination -h
  obtain ⟨s₀, s₀', hne⟩ := G.exists_polar_ne
  have hφ : (φ₂ - 1) * k = 0 := by
    have h := hBs 1 s₀ s₀'
    rw [hB1, hB1, hB1, G.Nm_add] at h
    have : (φ₂ - 1) * k * (G.trF (G.sharp s₀ * s₀') + G.trF (G.sharp s₀' * s₀)) = 0 := by
      linear_combination h
    exact (mul_eq_zero.1 this).resolve_right hne
  have hB1z : ∀ s, B 1 s = 0 := fun s => by rw [hB1, hφ]; ring
  have hsq : ∀ x : F, ∀ s, B (x ^ 2) s = 0 := by
    intro x s
    by_cases hx : x = 0
    · subst hx; rw [zero_pow two_ne_zero]; exact hB0 s
    · have h := hBτ x⁻¹ (inv_ne_zero hx) 1 (G.θ x * s)
      rw [show G.θ x⁻¹ * (G.θ x * s) = s by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, one_mul], hB1z, mul_zero,
        show ((x⁻¹) ^ 2)⁻¹ * 1 = x ^ 2 by field_simp] at h
      exact h
  intro c s
  have hc : ((c + 1) / 2) ^ 2 + (-(((c - 1) / 2) ^ 2)) = c := by field_simp; ring
  have key := hBc (((c + 1) / 2) ^ 2) (-(((c - 1) / 2) ^ 2)) s
  rw [hc, hBneg, hsq, hsq] at key
  simp only [hB] at key
  linear_combination key

end Funcs

end CFSG.GH74.GLS.Stage4.Hex
