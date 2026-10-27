module

public import CFSG.GH74.GLS.Stage4.HexCD4Gal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open Polynomial

namespace CFSG.GH74.GLS.Stage4.Hex

namespace GalData

variable {F K : Type} [Field F] [Field K]

def expo (q : ℕ) : Fin 6 → ℕ := ![2, 1 + q, 1 + q * q, 2 * q, q + q * q, 2 * (q * q)]

theorem expo_inj (q : ℕ) (hq : 3 ≤ q) : Function.Injective (expo q) := by
  intro i j h
  have h1 : q < q * q := by nlinarith
  have h2 : 2 * q < 1 + q * q := by nlinarith
  fin_cases i <;> fin_cases j <;> simp [expo] at h ⊢ <;> nlinarith

theorem expo_lt (q : ℕ) (hq : 3 ≤ q) (k : Fin 6) : expo q k < q ^ 3 := by
  have h1 : q < q * q := by nlinarith
  have h3 : q * q * 3 ≤ q ^ 3 := by nlinarith
  fin_cases k <;> simp [expo] <;> nlinarith

theorem expo_dvd (q : ℕ) (hq : 3 ≤ q) (k : Fin 6) (h : (q ^ 2 + q + 1) ∣ (expo q k + 1)) :
    k = 4 := by
  obtain ⟨t, ht⟩ := h
  have h1 : q < q * q := by nlinarith
  have hN : 13 ≤ q ^ 2 + q + 1 := by nlinarith
  fin_cases k <;> simp [expo] at ht ⊢
  · rcases t with _ | t <;> nlinarith
  · rcases t with _ | t <;> nlinarith
  · rcases t with _ | t <;> nlinarith
  · rcases t with _ | t <;> nlinarith
  · rcases t with _ | _ | t <;> nlinarith

theorem poly_indep {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : ι → ℕ) (he : Function.Injective e) (hlt : ∀ k, e k < Nat.card K) (c : ι → K)
    (h : ∀ s : K, ∑ k, c k * s ^ e k = 0) : ∀ k, c k = 0 := by
  classical
  have := Fintype.ofFinite K
  let P : K[X] := ∑ k, C (c k) * X ^ e k
  have hdeg : P.natDegree < Fintype.card K := by
    have h1 : P.natDegree ≤ Nat.card K - 1 :=
      natDegree_sum_le_of_forall_le _ _ (fun k _ =>
        (natDegree_C_mul_X_pow_le _ _).trans (by have := hlt k; omega))
    have : 0 < Nat.card K := Nat.card_pos
    rw [← Nat.card_eq_fintype_card]
    omega
  have hzero : P = 0 := by
    apply Polynomial.eq_zero_of_forall_eval_zero_of_natDegree_lt_card P _
    · rw [Cardinal.mk_fintype]; exact_mod_cast hdeg
    intro x
    simp [P, eval_finsetSum, h x]
  intro k₀
  have hc : P.coeff (e k₀) = c k₀ := by
    simp only [P, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    rw [Finset.sum_eq_single k₀]
    · simp
    · intro k _ hk
      have : e k₀ ≠ e k := fun h => hk (he h).symm
      simp [this]
    · simp
  rw [hzero] at hc
  simpa using hc.symm

theorem bil_rep (G : GalData F K) (B : K → K → K)
    (hadd1 : ∀ s s' t, B (s + s') t = B s t + B s' t)
    (hadd2 : ∀ s t t', B s (t + t') = B s t + B s t')
    (hhom1 : ∀ (c : F) s t, B (G.θ c * s) t = G.θ c * B s t)
    (hhom2 : ∀ (c : F) s t, B s (G.θ c * t) = G.θ c * B s t) :
    ∃ b : Fin 3 → Fin 3 → K, ∀ s t,
      B s t = b 0 0 * s * t + b 0 1 * s * G.σ t + b 0 2 * s * G.σ (G.σ t)
        + b 1 0 * G.σ s * t + b 1 1 * G.σ s * G.σ t + b 1 2 * G.σ s * G.σ (G.σ t)
        + b 2 0 * G.σ (G.σ s) * t + b 2 1 * G.σ (G.σ s) * G.σ t
        + b 2 2 * G.σ (G.σ s) * G.σ (G.σ t) := by
  classical
  have h1 : ∀ t, ∃ a₀ a₁ a₂ : K, ∀ s, B s t = a₀ * s + a₁ * G.σ s + a₂ * G.σ (G.σ s) := fun t =>
    G.lin_rep (fun s => B s t) (fun s s' => hadd1 s s' t) (fun c s => hhom1 c s t)
  choose A0 A1 A2 hA using h1
  have hsum : ∀ t t', ∀ s, (A0 (t + t') - A0 t - A0 t') * s + (A1 (t + t') - A1 t - A1 t') * G.σ s
      + (A2 (t + t') - A2 t - A2 t') * G.σ (G.σ s) = 0 := by
    intro t t' s
    have e1 := hA (t + t') s
    have e2 := hA t s
    have e3 := hA t' s
    have e4 := hadd2 s t t'
    linear_combination e4 - e1 + e2 + e3
  have hsumh : ∀ (c : F) t, ∀ s, (A0 (G.θ c * t) - G.θ c * A0 t) * s
      + (A1 (G.θ c * t) - G.θ c * A1 t) * G.σ s
      + (A2 (G.θ c * t) - G.θ c * A2 t) * G.σ (G.σ s) = 0 := by
    intro c t s
    have e1 := hA (G.θ c * t) s
    have e2 := hA t s
    have e4 := hhom2 c s t
    linear_combination e4 - e1 + G.θ c * e2
  have hA0 : ∃ b₀ b₁ b₂ : K, ∀ t, A0 t = b₀ * t + b₁ * G.σ t + b₂ * G.σ (G.σ t) := by
    refine G.lin_rep A0 (fun t t' => ?_) (fun c t => ?_)
    · have := (G.indep3 _ _ _ (hsum t t')).1; linear_combination this
    · have := (G.indep3 _ _ _ (hsumh c t)).1; linear_combination this
  have hA1 : ∃ b₀ b₁ b₂ : K, ∀ t, A1 t = b₀ * t + b₁ * G.σ t + b₂ * G.σ (G.σ t) := by
    refine G.lin_rep A1 (fun t t' => ?_) (fun c t => ?_)
    · have := (G.indep3 _ _ _ (hsum t t')).2.1; linear_combination this
    · have := (G.indep3 _ _ _ (hsumh c t)).2.1; linear_combination this
  have hA2 : ∃ b₀ b₁ b₂ : K, ∀ t, A2 t = b₀ * t + b₁ * G.σ t + b₂ * G.σ (G.σ t) := by
    refine G.lin_rep A2 (fun t t' => ?_) (fun c t => ?_)
    · have := (G.indep3 _ _ _ (hsum t t')).2.2; linear_combination this
    · have := (G.indep3 _ _ _ (hsumh c t)).2.2; linear_combination this
  obtain ⟨b00, b01, b02, hb0⟩ := hA0
  obtain ⟨b10, b11, b12, hb1⟩ := hA1
  obtain ⟨b20, b21, b22, hb2⟩ := hA2
  refine ⟨![![b00, b01, b02], ![b10, b11, b12], ![b20, b21, b22]], fun s t => ?_⟩
  rw [hA t s, hb0, hb1, hb2]
  simp
  ring

theorem weight_dvd (G : GalData F K) (e : ℕ)
    (h : ∀ ρ : Kˣ, ∃ x : Fˣ, (ρ : K) ^ (2 * e) = ((ρ : K) ^ 2)⁻¹ * (G.θ (x : F) ^ 2)⁻¹) :
    (G.q ^ 2 + G.q + 1) ∣ (e + 1) := by
  classical
  have := G.finiteK
  have := Fintype.ofFinite K
  have hq := G.hq
  have : IsCyclic Kˣ := inferInstance
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hcard : Nat.card Kˣ = G.q ^ 3 - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, G.hK]
  obtain ⟨x, hx⟩ := h g
  have hxq : G.θ (x : F) ^ (G.q - 1) = 1 := by
    have h1 : (x : F) ^ (G.q - 1) = 1 := by
      have hx0 : (x : F) ≠ 0 := x.ne_zero
      have := G.pow_card_F x
      have h2 : (x : F) ^ G.q = (x : F) ^ (G.q - 1) * x := by
        rw [← pow_succ]; congr 1; omega
      rw [h2] at this
      exact mul_right_cancel₀ hx0 (by rw [this, one_mul])
    rw [← map_pow, h1, map_one]
  have hg0 : ((g : K)) ≠ 0 := g.ne_zero
  have hpow : (g : K) ^ ((2 * e + 2) * (G.q - 1)) = 1 := by
    have h3 : (g : K) ^ (2 * e + 2) = (G.θ (x : F) ^ 2)⁻¹ := by
      rw [pow_add, hx]
      field_simp
    rw [pow_mul, h3, inv_pow, ← pow_mul, mul_comm 2 (G.q - 1), pow_mul, hxq]
    simp
  have hdvd : Nat.card Kˣ ∣ (2 * e + 2) * (G.q - 1) := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one (by ext; simpa using hpow)
  rw [hcard] at hdvd
  have hfac : G.q ^ 3 - 1 = (G.q - 1) * (G.q ^ 2 + G.q + 1) := by
    obtain ⟨r, hr⟩ : ∃ r, G.q = r + 1 := ⟨G.q - 1, by omega⟩
    rw [hr]
    apply Nat.sub_eq_of_eq_add
    simp only [Nat.add_sub_cancel]
    ring
  rw [hfac, mul_comm (2 * e + 2)] at hdvd
  have h1 : (G.q ^ 2 + G.q + 1) ∣ (2 * e + 2) :=
    Nat.dvd_of_mul_dvd_mul_left (by omega) hdvd
  have hodd : Nat.Coprime (G.q ^ 2 + G.q + 1) 2 := by
    apply Odd.coprime_two_right
    rcases Nat.even_mul_succ_self G.q with ⟨m, hm⟩
    exact ⟨m, by nlinarith⟩
  have h2 : (G.q ^ 2 + G.q + 1) ∣ 2 * (e + 1) := by
    have : 2 * e + 2 = 2 * (e + 1) := by ring
    rwa [this] at h1
  exact hodd.dvd_of_dvd_mul_left h2

theorem quad_monomial (G : GalData F K) (h2 : (2 : K) ≠ 0) (Q : K → K) (B : K → K → K)
    (hQ : ∀ s s', Q (s + s') = Q s + Q s' + B s s')
    (hadd1 : ∀ s s' t, B (s + s') t = B s t + B s' t)
    (hadd2 : ∀ s t t', B s (t + t') = B s t + B s t')
    (hhom1 : ∀ (c : F) s t, B (G.θ c * s) t = G.θ c * B s t)
    (hhom2 : ∀ (c : F) s t, B s (G.θ c * t) = G.θ c * B s t)
    (hQhom : ∀ (c : F) s, Q (G.θ c * s) = G.θ c ^ 2 * Q s)
    (hcov : ∀ ρ : Kˣ, ∃ x : Fˣ, ∀ s,
      Q ((ρ : K) ^ 2 * s) = ((ρ : K) ^ 2)⁻¹ * (G.θ (x : F) ^ 2)⁻¹ * Q s) :
    ∃ κ : K, ∀ s, Q s = κ * (G.σ s * G.σ (G.σ s)) := by
  classical
  have := G.finiteK
  have hq := G.hq
  obtain ⟨b, hb⟩ := G.bil_rep B hadd1 hadd2 hhom1 hhom2
  have hBQ : ∀ s, B s s = 2 * Q s := by
    intro s
    have e1 := hQ s s
    have e2 := hQhom 2 s
    rw [map_ofNat, two_mul] at e2
    linear_combination e2 - e1
  let c : Fin 6 → K := fun k =>
    (![b 0 0, b 0 1 + b 1 0, b 0 2 + b 2 0, b 1 1, b 1 2 + b 2 1, b 2 2] k) / 2
  have hQs : ∀ s, Q s = ∑ k, c k * s ^ expo G.q k := by
    intro s
    apply mul_left_cancel₀ h2
    rw [← hBQ s, hb s s, Fin.sum_univ_six]
    simp only [c, expo, G.hσ]
    simp
    field_simp
    ring
  have hind : ∀ ρ : Kˣ, ∀ k, c k * ((ρ : K) ^ (2 * expo G.q k) - ((ρ : K) ^ 2)⁻¹ *
      ((G.θ (hcov ρ).choose : K) ^ 2)⁻¹) = 0 := by
    intro ρ
    refine poly_indep (expo G.q) (expo_inj G.q hq) (fun k => by rw [G.hK]; exact expo_lt G.q hq k)
      _ (fun s => ?_)
    have h1 := hcov ρ
    have hx := h1.choose_spec s
    rw [hQs, hQs] at hx
    simp only [mul_pow, ← pow_mul, Finset.mul_sum] at hx
    rw [← sub_eq_zero] at hx
    rw [← hx, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hck : ∀ k : Fin 6, k ≠ 4 → c k = 0 := by
    intro k hk
    by_contra hne
    apply hk
    apply expo_dvd G.q hq k
    apply G.weight_dvd (expo G.q k)
    intro ρ
    refine ⟨(hcov ρ).choose, ?_⟩
    rcases mul_eq_zero.1 (hind ρ k) with h | h
    · exact absurd h hne
    · exact sub_eq_zero.1 h
  refine ⟨c 4, fun s => ?_⟩
  rw [hQs, Fin.sum_univ_six, hck 0 (by decide), hck 1 (by decide), hck 2 (by decide),
    hck 3 (by decide), hck 5 (by decide), G.hσ, G.hσ, ← pow_mul]
  simp only [zero_mul, zero_add, add_zero]
  have e4 : expo G.q 4 = G.q + G.q * G.q := rfl
  rw [e4, pow_add]

end GalData

end CFSG.GH74.GLS.Stage4.Hex
