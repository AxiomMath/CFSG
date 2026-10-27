module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcCentTwAbstract

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross
  (mactC mactCHom mactC_add mactC_one mactC_mul mactC_one_sub mactC_one_vec
    eightyOne_dvd_of_pair_ab lift_centralizer_of_solve_ab solve_group_ab)

section Local

variable {G : Type} [Group G] {W : Type} [Group W] {r : ℕ} {C : Type} [CommGroup C]
variable (ι : (Fin r → C) →* G) (π : G →* W) (A : W → Matrix (Fin r) (Fin r) ℤ)
variable (hι : Function.Injective ι) (hιπ : ∀ t, π (ι t) = 1)
  (hconj : ∀ (g : G) (t : Fin r → C), g * ι t * g⁻¹ = ι (mactC (A (π g)) t))

include hι hιπ hconj in
theorem caseA_loc (x y : W) (s gx gy : G) (hdec : ∃ h, s = ι h * gx)
    (hs : π s = x) (hgx : π gx = x) (hgy : π gy = y)
    (hcomm : gy * gx = gx * gy) (hgx3 : gx ^ 3 = 1) (hs3 : s ^ 3 = 1)
    (Φ Ψ : Matrix (Fin r) (Fin r) ℤ)
    (hid : 1 - A y = (1 - A x) * Φ + Ψ * (1 + A x + A x * A x))
    (ω : C) (hω : orderOf ω = 3) (c₁ c₂ : Fin r → ℤ) (p₁ p₂ : Fin r)
    (hf₁ : ∀ i, (3 : ℤ) ∣ ((A x).mulVec c₁) i - c₁ i)
    (hf₂ : ∀ i, (3 : ℤ) ∣ ((A x).mulVec c₂) i - c₂ i)
    (h11 : c₁ p₁ = 1) (h12 : c₂ p₁ = 0) (h21 : c₁ p₂ = 0) (h22 : c₂ p₂ = 1)
    (hQ : 9 ∣ Nat.card (Subgroup.closure ({x, y} : Set W))) :
    81 ∣ Nat.card (Subgroup.centralizer ({s} : Set G)) := by
  obtain ⟨h, hsh⟩ := hdec
  have hcube := cube_of_conj ι (mactCHom (C := C) (A x)) gx h
    (fun t => by have := hconj gx t; rwa [hgx] at this) hgx3
  rw [← hsh, hs3, ← map_one ι] at hcube
  have hN : mactC (1 + A x + A x * A x) h = 1 := by
    have := hι hcube
    rw [mactC_add, mactC_add, mactC_one, mactC_mul]
    simpa [NaturalModuleCensus.ExcCross.mactCHom_apply, mul_assoc] using this.symm
  have ha : mactC Φ h * (mactC (A x) (mactC Φ h))⁻¹ =
      h * (mactC (A y) h)⁻¹ * (1 : Fin r → C)⁻¹ := by
    have h1 : mactC (1 - A y) h = h * (mactC (A y) h)⁻¹ := mactC_one_sub (A y) h
    have h2 : mactC (1 - A x) (mactC Φ h) = mactC Φ h * (mactC (A x) (mactC Φ h))⁻¹ :=
      mactC_one_sub (A x) _
    rw [← h2, inv_one, mul_one, ← h1, hid, mactC_add, mactC_mul Ψ, hN, mactC_one_vec, mul_one,
      mactC_mul]
  have hu : gy * gx * gy⁻¹ = ι 1 * gx := by
    rw [map_one, one_mul, mul_inv_eq_iff_eq_mul, hcomm]
  have ha' : mactC Φ h * (mactC (A (π gx)) (mactC Φ h))⁻¹ =
      h * (mactC (A (π gy)) h)⁻¹ * (1 : Fin r → C)⁻¹ := by
    rw [hgx, hgy]; exact ha
  obtain ⟨hc, hcy⟩ := lift_centralizer_of_solve_ab ι π A hιπ hconj h 1 _ hsh hu ha'
  exact eightyOne_dvd_of_pair_ab ι π A hι hιπ hconj x y s _ hs hc (hcy.trans hgy) ω hω c₁ c₂ p₁ p₂
    hf₁ hf₂ h11 h12 h21 h22 hQ

section Cyclic

variable [IsCyclic C]

include hι hιπ hconj in
theorem caseB_loc {n : ℕ} (x : W) (ys : Fin n → W) (s gx : G) (hdec : ∃ h, s = ι h * gx)
    (hs : π s = x) (hgx : π gx = x)
    (hlift : ∀ i, ∃ (gy : G) (u : Fin r → C), π gy = ys i ∧ u * u = 1 ∧
      gy * gx * gy⁻¹ = ι u * gx)
    (Ξ : Matrix (Fin r) (Fin r) ℤ) (hΞ : (1 - A x) * Ξ = (3 : ℤ) • 1)
    (hsolve : ∀ c : Fin r → ℤ, ∃ i : Fin n, ∃ d : Fin r → ℤ,
      (1 - A x).mulVec d = (1 - A (ys i)).mulVec c)
    (ω : C) (hω : orderOf ω = 3) (c₁ c₂ : Fin r → ℤ) (p₁ p₂ : Fin r)
    (hf₁ : ∀ i, (3 : ℤ) ∣ ((A x).mulVec c₁) i - c₁ i)
    (hf₂ : ∀ i, (3 : ℤ) ∣ ((A x).mulVec c₂) i - c₂ i)
    (h11 : c₁ p₁ = 1) (h12 : c₂ p₁ = 0) (h21 : c₁ p₂ = 0) (h22 : c₂ p₂ = 1)
    (hQ : ∀ i, 9 ∣ Nat.card (Subgroup.closure ({x, ys i} : Set W))) :
    81 ∣ Nat.card (Subgroup.centralizer ({s} : Set G)) := by
  obtain ⟨h, hsh⟩ := hdec
  choose gy u hgy hu1 hu2 using hlift
  obtain ⟨i, a, ha⟩ := solve_group_ab (C := C) (A x) (fun i => A (ys i)) Ξ hΞ u hu1 hsolve h
  have ha' : a * (mactC (A (π gx)) a)⁻¹ =
      h * (mactC (A (π (gy i))) h)⁻¹ * (u i)⁻¹ := by
    rw [hgx, hgy i]; exact ha
  obtain ⟨hc, hcy⟩ := lift_centralizer_of_solve_ab ι π A hιπ hconj h (u i) a hsh (hu2 i) ha'
  exact eightyOne_dvd_of_pair_ab ι π A hι hιπ hconj x (ys i) s _ hs hc (hcy.trans (hgy i)) ω hω
    c₁ c₂ p₁ p₂ hf₁ hf₂ h11 h12 h21 h22 (hQ i)

end Cyclic

end Local

end CFSG.HardMathSupport.Curtis.UnitaryLevi

end
