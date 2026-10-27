module

public import CFSG.GH74.GLS.Stage4.HexCD4Alg4
public import CFSG.GH74.GLS.Stage4.HexCD4Alg3

public section

open Polynomial

namespace CFSG.GH74.GLS.Stage4.Hex

variable {F K : Type} [Field F] [Field K]

theorem cube_add (h3 : (3 : F) = 0) (x y : F) : (x + y) ^ 3 = x ^ 3 + y ^ 3 := by
  have hcp : CharP F 3 := (CharP.charP_iff_prime_eq_zero Nat.prime_three).2 h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact add_pow_char (R := F) (p := 3) x y

theorem cube_inj (h3 : (3 : F) = 0) {x y : F} (h : x ^ 3 = y ^ 3) : x = y := by
  have hcp : CharP F 3 := (CharP.charP_iff_prime_eq_zero Nat.prime_three).2 h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h0 : (x - y) ^ 3 = 0 := by rw [sub_pow_char (R := F) (p := 3), h, sub_self]
  exact sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h0)

theorem exists_cube_root [Finite F] (h3 : (3 : F) = 0) (y : F) : ∃ x : F, x ^ 3 = y := by
  have hinj : Function.Injective (fun x : F => x ^ 3) := fun x y h => cube_inj h3 h
  exact Finite.injective_iff_surjective.1 hinj y

namespace GalData

variable (G : GalData F K)

theorem Nm_mul (s t : K) : G.Nm (s * t) = G.Nm s * G.Nm t := by
  apply G.θ.injective
  rw [map_mul, G.θ_Nm, G.θ_Nm, G.θ_Nm]
  simp only [norm', map_mul]; ring

theorem exists_sq_not_fixed : ∃ x : K, G.σ (x ^ 2) ≠ x ^ 2 := by
  classical
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have := G.finiteK
  have := Fintype.ofFinite K
  have hq := G.hq
  have h' : ∀ x : K, x ^ (2 * G.q) = x ^ 2 := by
    intro x
    have := hcon x
    rwa [G.hσ, ← pow_mul] at this
  let P : K[X] := X ^ (2 * G.q) - X ^ 2
  have hdeg : P.natDegree = 2 * G.q := by
    show (X ^ (2 * G.q) - X ^ 2 : K[X]).natDegree = 2 * G.q
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp
    omega
  have hlt : P.natDegree < Fintype.card K := by
    rw [hdeg, ← Nat.card_eq_fintype_card, G.hK]
    have h1 : 2 * G.q < G.q * G.q := by nlinarith
    have h2 : G.q * G.q ≤ G.q ^ 3 := by
      calc G.q * G.q = G.q ^ 2 := by ring
        _ ≤ G.q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    exact lt_of_lt_of_le h1 h2
  have hzero : P = 0 := by
    apply Polynomial.eq_zero_of_forall_eval_zero_of_natDegree_lt_card P _
    · rw [Cardinal.mk_fintype]; exact_mod_cast hlt
    intro x
    simp [P, h' x]
  have hc : P.coeff (2 * G.q) = 1 := by
    have h1 : 2 * G.q ≠ 2 := by omega
    simp [P, coeff_sub, coeff_X_pow, h1]
  rw [hzero] at hc
  simp at hc

end GalData

section Funcs

variable (G : GalData F K) {a2 a4 : K → K → F} {ℓ : K → K → K} {A2 A4 : F → K → F} {g : F → K → K}
  (H : D4Funcs G a2 a4 ℓ A2 A4 g)

include H in
theorem d4_A2_p3 (h3 : (3 : F) = 0) {k : F} (hκ : ∀ s, g 1 s = G.θ k * G.sharp s)
    (ha2 : ∀ s t, a2 s t = k * G.trF (G.sharp s * t))
    (hcov : ∀ ρ : Kˣ, ∃ χ : F, χ ≠ 0 ∧
      ∀ c s, A2 (χ * c) ((ρ : K) ^ 2 * s) = χ⁻¹ * A2 c s) :
    ∀ c s, A2 c s = c * (k * G.Nm s) := by
  have := G.finiteF
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
  set ε : K → F := fun s => A2 1 s - k * G.Nm s with hε
  have hε_add : ∀ s s', ε (s + s') = ε s + ε s' := by
    intro s s'; simp only [hε]; rw [hadd, G.Nm_add]; ring
  have hε0 : ε 0 = 0 := by
    have := hε_add 0 0
    rw [add_zero] at this
    exact add_eq_left.1 this.symm
  have hε_hom : ∀ x : F, ∀ s, ε (G.θ x * s) = x ^ 3 * ε s := by
    intro x s
    by_cases hx : x = 0
    · subst hx
      rw [map_zero, zero_mul, hε0]; ring
    · simp only [hε]; rw [hhom x hx s, G.Nm_smul]; ring
  have hρ : ∀ ρ : Kˣ, ∃ χ : F, χ ≠ 0 ∧ ∀ s, ε ((ρ : K) ^ 2 * s) = (χ ^ 2)⁻¹ * ε s := by
    intro ρ
    obtain ⟨χ, hχ, hc⟩ := hcov ρ
    refine ⟨χ, hχ, fun s => ?_⟩
    have h1 := hc 1 s
    rw [H.A2_eq G (χ * 1) ((ρ : K) ^ 2 * s)] at h1
    have hA : ∀ s, A2 1 ((ρ : K) ^ 2 * s) = (χ ^ 2)⁻¹ * A2 1 s := by
      intro s
      have h1 := hc 1 s
      rw [H.A2_eq G (χ * 1) ((ρ : K) ^ 2 * s)] at h1
      field_simp at h1 ⊢
      linear_combination h1
    have hψ : ∀ s, ε ((ρ : K) ^ 2 * s) - (χ ^ 2)⁻¹ * ε s =
        ((χ ^ 2)⁻¹ - G.Nm ρ ^ 2) * k * G.Nm s := by
      intro s
      simp only [hε]
      rw [hA s, G.Nm_mul ((ρ : K) ^ 2) s, pow_two (ρ : K), G.Nm_mul ρ ρ]
      ring
    obtain ⟨s₀, s₀', hne⟩ := G.exists_polar_ne
    have hlk : ((χ ^ 2)⁻¹ - G.Nm ρ ^ 2) * k = 0 := by
      have e := hψ (s₀ + s₀')
      have e₁ := hψ s₀
      have e₂ := hψ s₀'
      rw [mul_add, hε_add, hε_add, G.Nm_add] at e
      have : ((χ ^ 2)⁻¹ - G.Nm ρ ^ 2) * k *
          (G.trF (G.sharp s₀ * s₀') + G.trF (G.sharp s₀' * s₀)) = 0 := by
        linear_combination e₁ + e₂ - e
      exact (mul_eq_zero.1 this).resolve_right hne
    have := hψ s
    rw [hlk, zero_mul] at this
    linear_combination this
  choose ε' hε' using fun s => exists_cube_root h3 (ε s)
  have hε'_add : ∀ s s', ε' (s + s') = ε' s + ε' s' := fun s s' =>
    cube_inj h3 (by rw [hε', cube_add h3, hε', hε', hε_add])
  have hε'_hom : ∀ (x : F) s, ε' (G.θ x * s) = x * ε' s := fun x s =>
    cube_inj h3 (by rw [hε', hε_hom, mul_pow, hε'])
  obtain ⟨e, he⟩ := G.dual_rep ε' hε'_add hε'_hom
  obtain ⟨x₀, hx₀⟩ := G.exists_sq_not_fixed
  have hx₀0 : x₀ ≠ 0 := by
    rintro rfl
    apply hx₀
    simp
  obtain ⟨χ, hχ, hεχ⟩ := hρ (Units.mk0 x₀ hx₀0)
  simp only [Units.val_mk0] at hεχ
  obtain ⟨ν, hν⟩ := exists_cube_root h3 ((χ ^ 2)⁻¹)
  have hε'ρ : ∀ s, ε' (x₀ ^ 2 * s) = ν * ε' s := fun s =>
    cube_inj h3 (by rw [hε', hεχ, mul_pow, hν, hε'])
  have hee : e * x₀ ^ 2 = G.θ ν * e := by
    apply G.eq_of_trF_eq
    intro s
    have h1 := hε'ρ s
    rw [he, he, ← G.trF_smul] at h1
    rw [show e * x₀ ^ 2 * s = e * (x₀ ^ 2 * s) by ring]
    rw [h1]
    congr 1; ring
  have he0 : e = 0 := by
    by_contra hne
    apply hx₀
    have : x₀ ^ 2 = G.θ ν := by
      have h' : e * x₀ ^ 2 = e * G.θ ν := by rw [hee]; ring
      exact mul_left_cancel₀ hne h'
    rw [this, G.σ_θ]
  have hε'0 : ∀ s, ε' s = 0 := fun s => by rw [he, he0, zero_mul, G.trF_zero]
  have hε00 : ∀ s, A2 1 s = k * G.Nm s := fun s => by
    have := hε' s
    rw [hε'0, zero_pow (by norm_num)] at this
    linear_combination -this
  intro c s
  rw [H.A2_eq G c s, hε00 s]

end Funcs

theorem d4_formulas' (G : GalData F K) (h2 : (2 : F) ≠ 0)
    {a2 a4 : K → K → F} {ℓ : K → K → K} {A2 A4 : F → K → F} {g : F → K → K}
    (H : D4Funcs G a2 a4 ℓ A2 A4 g)
    (hcov : ∀ ρ : Kˣ, ∃ χ : Fˣ, ∀ c s, g ((χ : F) * c) ((ρ : K) ^ 2 * s) =
      ((ρ : K) ^ 2)⁻¹ * (G.θ (χ : F))⁻¹ * g c s)
    {φ₂ : F} (hslot : ∀ s, φ₂ * A2 1 s + a4 (-s) s = A4 (-1) (-s))
    (hA2gen : ∀ {k : F}, (∀ s, g 1 s = G.θ k * G.sharp s) →
      (∀ s t, a2 s t = k * G.trF (G.sharp s * t)) → ∀ c s, A2 c s = c * (k * G.Nm s)) :
    ∃ k : F, (∀ s, g 1 s = G.θ k * G.sharp s) ∧ (∀ s t, ℓ s t = G.θ k * G.cross s t) ∧
      (∀ s t, a2 s t = k * G.trF (G.sharp s * t)) ∧ (∀ s t, a4 s t = k * G.trF (s * G.sharp t)) ∧
      (∀ c s, A2 c s = c * (k * G.Nm s)) ∧ (∀ c s, A4 c s = 2 * k * c ^ 2 * G.Nm s) := by
  obtain ⟨κ, hκ⟩ := d4_Q G H (G.two_ne_zero_K h2) hcov
  have hκ' : ∀ s, g 1 s = κ * G.sharp s := hκ
  have hσκ : G.σ κ = κ := d4_kappa G H hκ'
  obtain ⟨k, hk⟩ := G.fixed_eq hσκ
  subst hk
  have hA2 := hA2gen hκ (fun s t => d4_a2 G H hκ s t)
  exact ⟨k, hκ, H.ℓ_eq G hκ, fun s t => d4_a2 G H hκ s t, fun s t => d4_a4 G H h2 hκ s t, hA2,
    d4_A4 G H h2 hκ (fun s t => d4_a4 G H h2 hκ s t) hA2 hslot⟩

end CFSG.GH74.GLS.Stage4.Hex
