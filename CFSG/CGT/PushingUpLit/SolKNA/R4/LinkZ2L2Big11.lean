module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big5
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big6

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W CFSG.GorensteinWalter
open CFSG.Blueprint

section Outer

variable {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F]

theorem exists_inner_of_psl (E : PGamEmb X F) {g : PGammaL2 F} (h1 : g.right = 1)
    (h2 : g.left ∈ pslRange F) : ∃ x ∈ genFittingFStar X, E.ρ (MulAut.conj x) = g := by
  obtain ⟨s, hs⟩ := h2
  obtain ⟨n, hn, hnρ⟩ := E.onto s
  refine ⟨n, hn, ?_⟩
  rw [hnρ, hs]
  exact (TL4.MF163.eq_inl_of_right_eq_one h1).symm

theorem exists_inner_of_quot (E : PGamEmb X F) {b : X} {g : PGammaL2 F}
    (h1 : (g * (E.ρ (MulAut.conj b))⁻¹).right = 1)
    (h2 : (g * (E.ρ (MulAut.conj b))⁻¹).left ∈ pslRange F) :
    ∃ x : X, E.ρ (MulAut.conj x) = g := by
  obtain ⟨n, -, hnρ⟩ := exists_inner_of_psl E h1 h2
  refine ⟨n * b, ?_⟩
  calc E.ρ (MulAut.conj (n * b)) = E.ρ (MulAut.conj n * MulAut.conj b) := by rw [map_mul]
    _ = E.ρ (MulAut.conj n) * E.ρ (MulAut.conj b) := by rw [map_mul]
    _ = (g * (E.ρ (MulAut.conj b))⁻¹) * E.ρ (MulAut.conj b) := by rw [hnρ]
    _ = g := by group

theorem inner_quot_mem (E : PGamEmb X F) (hidx : (genFittingFStar X).index ≤ 2) {b x : X}
    (hb : (E.ρ (MulAut.conj b)).right ≠ 1) (hx : (E.ρ (MulAut.conj x)).right ≠ 1) :
    (E.ρ (MulAut.conj x) * (E.ρ (MulAut.conj b))⁻¹).right = 1 ∧
      (E.ρ (MulAut.conj x) * (E.ρ (MulAut.conj b))⁻¹).left ∈ pslRange F := by
  have hb' : b ∉ genFittingFStar X := by
    intro hbm
    obtain ⟨g, hg⟩ := E.inner b hbm
    exact hb (by rw [hg]; rfl)
  have hx' : x ∉ genFittingFStar X := by
    intro hxm
    obtain ⟨g, hg⟩ := E.inner x hxm
    exact hx (by rw [hg]; rfl)
  have hidx2 : (genFittingFStar X).index = 2 := by
    have hne0 : (genFittingFStar X).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hne1 : (genFittingFStar X).index ≠ 1 := by
      intro h
      rw [Subgroup.index_eq_one] at h
      exact hx' (h ▸ Subgroup.mem_top x)
    omega
  have hmem : x * b⁻¹ ∈ genFittingFStar X := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx2]
    exact ⟨fun h => absurd h hx', fun h => absurd ((genFittingFStar X).inv_mem_iff.mp h) hb'⟩
  obtain ⟨g', hg'⟩ := E.inner (x * b⁻¹) hmem
  have hconj : MulAut.conj x * (MulAut.conj b)⁻¹ = MulAut.conj (x * b⁻¹) := by
    rw [map_mul, map_inv]
  have hprod : E.ρ (MulAut.conj x) * (E.ρ (MulAut.conj b))⁻¹ =
      E.ρ (MulAut.conj (x * b⁻¹)) := by
    rw [← map_inv, ← map_mul, hconj]
  refine ⟨?_, ?_⟩
  · rw [hprod, hg']; rfl
  · rw [hprod, hg']
    exact ⟨g', rfl⟩

end Outer

section Numerics

variable {F : Type} [Field F] [Finite F]

theorem autU_zpow (σ : F ≃+* F) (x : Fˣ) (n : ℤ) : autU σ (x ^ n) = (autU σ x) ^ n :=
  map_zpow (Units.map σ.toRingHom.toMonoidHom) x n

theorem autU_pow_mem_pair {σ : F ≃+* F} {x : Fˣ}
    (h : autU σ x = x ∨ autU σ x = x⁻¹) (j : ℕ) :
    autU (σ ^ j) x = x ∨ autU (σ ^ j) x = x⁻¹ := by
  induction j with
  | zero => rw [pow_zero, autU_one_aut]; exact Or.inl rfl
  | succ j ih =>
    rw [pow_succ', autU_comp]
    rcases ih with h' | h'
    · rw [h']; exact h
    · rcases h with hh | hh
      · rw [h', autU_inv, hh]; exact Or.inr rfl
      · rw [h', autU_inv, hh, inv_inv]; exact Or.inl rfl

theorem pow_half_eq_neg_one_of_not_isSquare (h2 : (2 : F) ≠ 0) {u : Fˣ}
    (hu : ¬ IsSquare u) : u ^ (Nat.card Fˣ / 2) = -1 := by
  have hN : u ^ (Nat.card Fˣ / 2) ≠ 1 := fun h => hu ((isSquare_iff_pow_eq_one h2 u).mpr h)
  have h2N : 2 * (Nat.card Fˣ / 2) = Nat.card Fˣ := by
    have hdvd : 2 ∣ Nat.card Fˣ := by
      rw [← orderOf_units_neg_one h2]
      exact orderOf_dvd_natCard (-1 : Fˣ)
    exact Nat.mul_div_cancel' hdvd
  have hsq : (u ^ (Nat.card Fˣ / 2)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, h2N, pow_card_eq_one']
  rcases (unit_sq_eq_one_iff _).mp hsq with h | h
  · exact absurd h hN
  · exact h

theorem isSquare_iff_even_of_pow_eq_neg_one (h2 : (2 : F) ≠ 0) {u : Fˣ} {c d : ℕ}
    (hcd : c * d = Nat.card Fˣ / 2) (hu : u ^ c = -1) : IsSquare u ↔ Even d := by
  rw [isSquare_iff_pow_eq_one h2 u]
  have hpow : u ^ (Nat.card Fˣ / 2) = (-1 : Fˣ) ^ d := by
    rw [← hcd, pow_mul, hu]
  rw [hpow, ← zpow_natCast, ← orderOf_dvd_iff_zpow_eq_one, orderOf_units_neg_one h2,
    Int.natCast_dvd_natCast]
  exact even_iff_two_dvd.symm

theorem isSquare_mul_of_not_isSquare (h2 : (2 : F) ≠ 0) {a b : Fˣ} (ha : ¬ IsSquare a)
    (hb : ¬ IsSquare b) : IsSquare (a * b) := by
  rw [isSquare_iff_pow_eq_one h2, mul_pow, pow_half_eq_neg_one_of_not_isSquare h2 ha,
    pow_half_eq_neg_one_of_not_isSquare h2 hb]
  rw [neg_mul_neg, one_mul]

theorem not_isSquare_mul_of_isSquare (h2 : (2 : F) ≠ 0) {a b : Fˣ} (ha : IsSquare a)
    (hb : ¬ IsSquare b) : ¬ IsSquare (a * b) := by
  intro hab
  rw [isSquare_iff_pow_eq_one h2] at hab
  rw [isSquare_iff_pow_eq_one h2] at ha
  rw [mul_pow, ha, one_mul, pow_half_eq_neg_one_of_not_isSquare h2 hb] at hab
  exact units_neg_one_ne_one h2 hab

theorem card_units_eq_sq_sub_one {p f : ℕ} (hF : Nat.card F = p ^ f) (hf : Even f) :
    Nat.card Fˣ = p ^ (f / 2) * p ^ (f / 2) - 1 := by
  rw [card_units_eq_of_card hF]
  congr 1
  rw [← pow_add]
  congr 1
  obtain ⟨g, hg⟩ := hf
  omega

theorem autU_eq_pow {σ₀ : F ≃+* F} {q : ℕ} (hq : ∀ x : F, σ₀ x = x ^ q) (u : Fˣ) :
    autU σ₀ u = u ^ q := by
  apply Units.ext
  rw [autU_val, hq, Units.val_pow_eq_pow_val]

theorem q_mod_eight_of_dvd_add_one {q r : ℕ} (hr : 4 ≤ r) (h : 2 ^ (r - 1) ∣ q + 1) :
    q % 8 = 7 := by
  have h8 : 8 ∣ q + 1 := by
    have h3 : 3 ≤ r - 1 := by omega
    exact (Nat.pow_dvd_pow 2 h3).trans h
  have hmod : (q + 1) % 8 = 0 := Nat.dvd_iff_mod_eq_zero.mp h8
  have h1 : (q % 8 + 1) % 8 = 0 := by
    have := Nat.add_mod q 1 8
    rw [hmod] at this
    simpa using this.symm
  have hlt : q % 8 + 1 ≤ 8 := by have := Nat.mod_lt q (show 0 < 8 by norm_num); omega
  have hpos : 0 < q % 8 + 1 := by omega
  have hne : ¬ (q % 8 + 1 < 8) := by
    intro hlt'
    rw [Nat.mod_eq_of_lt hlt'] at h1
    omega
  omega

theorem q_mod_eight_of_dvd_sub_one {q r : ℕ} (hr : 4 ≤ r) (hq : 1 ≤ q)
    (h : 2 ^ (r - 1) ∣ q - 1) : q % 8 = 1 := by
  have h8 : 8 ∣ q - 1 := by
    have h3 : 3 ≤ r - 1 := by omega
    exact (Nat.pow_dvd_pow 2 h3).trans h
  have hmod : (q - 1) % 8 = 0 := Nat.dvd_iff_mod_eq_zero.mp h8
  calc q % 8 = ((q - 1) + 1) % 8 := by rw [Nat.sub_add_cancel hq]
    _ = ((q - 1) % 8 + 1) % 8 := by simp [Nat.add_mod]
    _ = 1 := by simp [hmod]

theorem unit_eq_neg_one_or_one_of_pow {u : Fˣ} {c k : ℕ} (hc : c % 4 = 2) (hu : u ^ c = 1)
    (hk : u ^ 2 ^ k = 1) : u = 1 ∨ u = -1 := by
  have hgcd : u ^ Nat.gcd c (2 ^ k) = 1 := pow_gcd_eq_one.mpr ⟨hu, hk⟩
  have hg : Nat.gcd c (2 ^ k) ∣ 2 := by
    obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Nat.gcd_dvd_right c (2 ^ k))
    rw [hjeq]
    have hj1 : j ≤ 1 := by
      by_contra hj'
      push Not at hj'
      have h4c : 4 ∣ c := by
        have h42j : 4 ∣ 2 ^ j := by
          have := Nat.pow_dvd_pow 2 hj'
          simpa using this
        exact h42j.trans (hjeq ▸ Nat.gcd_dvd_left c (2 ^ k))
      rw [Nat.dvd_iff_mod_eq_zero] at h4c
      omega
    have := Nat.pow_dvd_pow 2 hj1
    simpa using this
  rcases (Nat.dvd_prime Nat.prime_two).mp hg with h1 | h2
  · left; rw [h1] at hgcd; simpa using hgcd
  · rw [h2] at hgcd; exact (unit_sq_eq_one_iff u).mp hgcd

theorem pow_two_dvd_sq_sub_one_of_dvd_sub {r : ℕ} (hr : 2 ≤ r) {t : ℤ}
    (h : ((2 : ℤ) ^ (r - 1)) ∣ t - 1) : ((2 : ℤ) ^ r) ∣ t * t - 1 := by
  have h2 : (2 : ℤ) ∣ t + 1 := by
    have h2a : (2 : ℤ) ∣ t - 1 := by
      have hd : (2 : ℤ) ∣ (2 : ℤ) ^ (r - 1) := by
        have := Nat.pow_dvd_pow 2 (by omega : 1 ≤ r - 1)
        exact_mod_cast this
      exact hd.trans h
    obtain ⟨s, hs⟩ := h2a
    exact ⟨s + 1, by omega⟩
  have hmul : ((2 : ℤ) ^ r) ∣ (t - 1) * (t + 1) := by
    have he : ((2 : ℤ) ^ r) = (2 : ℤ) ^ (r - 1) * 2 := by
      conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ]
    rw [he]
    exact mul_dvd_mul h h2
  have hprod : (t - 1) * (t + 1) = t * t - 1 := by ring
  rwa [hprod] at hmul

theorem pow_two_dvd_sq_sub_one_of_dvd_add {r : ℕ} (hr : 2 ≤ r) {t : ℤ}
    (h : ((2 : ℤ) ^ (r - 1)) ∣ t + 1) : ((2 : ℤ) ^ r) ∣ t * t - 1 := by
  have h2 : (2 : ℤ) ∣ t - 1 := by
    have h2a : (2 : ℤ) ∣ t + 1 := by
      have hd : (2 : ℤ) ∣ (2 : ℤ) ^ (r - 1) := by
        have := Nat.pow_dvd_pow 2 (by omega : 1 ≤ r - 1)
        exact_mod_cast this
      exact hd.trans h
    obtain ⟨s, hs⟩ := h2a
    exact ⟨s - 1, by omega⟩
  have hmul : ((2 : ℤ) ^ r) ∣ (t - 1) * (t + 1) := by
    have he : ((2 : ℤ) ^ r) = 2 * (2 : ℤ) ^ (r - 1) := by
      conv_lhs => rw [show r = 1 + (r - 1) by omega, pow_add]
      norm_num
    rw [he]
    exact mul_dvd_mul h2 h
  have hprod : (t - 1) * (t + 1) = t * t - 1 := by ring
  rwa [hprod] at hmul

end Numerics

section AutFix

variable {F : Type} [Field F] [Finite F] {p f : ℕ}

theorem aut_sq_eq_one_of_fix [Fact p.Prime] (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (h4 : 4 ≤ p ^ f) (hf : Even f) {σ₀ : F ≃+* F} (hσ₀1 : σ₀ ≠ 1) (hσ₀2 : σ₀ * σ₀ = 1)
    (hq : ∀ x : F, σ₀ x = x ^ (p ^ (f / 2))) {r : ℕ} (hr : 4 ≤ r) (hdvd : 2 ^ r ∣ p ^ f - 1)
    (harith : ¬ 2 ^ (r + 1) ∣ p ^ f - 1) {x₀ : Fˣ} (hx₀ : orderOf x₀ = 2 ^ (r - 1))
    {τ : F ≃+* F} {k : ℕ} (hτ : τ ^ 2 ^ k = 1) (hfix : autU τ x₀ = x₀ ∨ autU τ x₀ = x₀⁻¹) :
    τ * τ = 1 := by
  by_contra hτ2
  let q : ℕ := p ^ (f / 2)
  have hqq : q * q = p ^ f := by
    change p ^ (f / 2) * p ^ (f / 2) = p ^ f
    rw [← pow_add]
    congr 1
    obtain ⟨g, hg⟩ := hf
    omega
  have hqodd : Odd q := by
    change Odd (p ^ (f / 2))
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  obtain ⟨m, -, hmeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hτ)
  have hm2 : 2 ≤ m := by
    by_contra hm
    push Not at hm
    have hd : orderOf τ ∣ 2 := by
      rw [hmeq]
      have := Nat.pow_dvd_pow 2 (by omega : m ≤ 1)
      simpa using this
    exact hτ2 (by rw [← sq]; exact orderOf_dvd_iff_pow_eq_one.mp hd)
  have hpowm : τ ^ 2 ^ m = 1 := by rw [← hmeq]; exact pow_orderOf_eq_one τ
  have hσ2 : τ ^ 2 ^ (m - 1) * τ ^ 2 ^ (m - 1) = 1 := by
    rw [← sq, ← pow_mul]
    have h2m : 2 ^ (m - 1) * 2 = 2 ^ m := by
      conv_rhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
    rw [h2m, hpowm]
  have hσne : τ ^ 2 ^ (m - 1) ≠ 1 := by
    intro h
    have hd : 2 ^ m ∣ 2 ^ (m - 1) := by
      rw [← hmeq]
      exact orderOf_dvd_of_pow_eq_one h
    have hle : 2 ^ m ≤ 2 ^ (m - 1) := Nat.le_of_dvd (Nat.pow_pos (by norm_num)) hd
    have hlt : 2 ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hσσ₀ : τ ^ 2 ^ (m - 1) = σ₀ := by
    rcases ringAut_sq_eq_one hF hp2 h4 hσ₀1 hσ₀2 hσ2 with h | h
    · exact absurd h hσne
    · exact h
  have hτ'sq : τ ^ 2 ^ (m - 2) * τ ^ 2 ^ (m - 2) = τ ^ 2 ^ (m - 1) := by
    rw [← sq, ← pow_mul]
    congr 1
    rw [show m - 1 = (m - 2) + 1 by omega, pow_succ]
  have hσ₀eq : σ₀ = τ ^ 2 ^ (m - 2) * τ ^ 2 ^ (m - 2) := (hτ'sq.trans hσσ₀).symm
  have hfix' : autU (τ ^ 2 ^ (m - 2)) x₀ = x₀ ∨ autU (τ ^ 2 ^ (m - 2)) x₀ = x₀⁻¹ :=
    autU_pow_mem_pair hfix (2 ^ (m - 2))
  obtain ⟨t, ht⟩ := MonoidHom.map_cyclic (Units.map (τ ^ 2 ^ (m - 2)).toRingHom.toMonoidHom)
  have ht' : ∀ x : Fˣ, autU (τ ^ 2 ^ (m - 2)) x = x ^ t := ht
  have hcomp : ∀ x : Fˣ, autU σ₀ x = x ^ (t * t) := by
    intro x
    rw [hσ₀eq, autU_comp, ht' x, autU_zpow, ht' x, ← zpow_mul]
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hordζ : orderOf ζ = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hζ
  have h1 : ζ ^ (t * t) = ζ ^ q := (hcomp ζ).symm.trans (autU_eq_pow hq ζ)
  have h1z : ζ ^ (t * t) = ζ ^ (q : ℤ) := by rw [zpow_natCast]; exact h1
  have hdvd_tq : (Nat.card Fˣ : ℤ) ∣ t * t - (q : ℤ) := by
    rw [← hordζ, orderOf_dvd_iff_zpow_eq_one, zpow_sub, h1z, mul_inv_cancel]
  have h2rN : ((2 : ℤ) ^ r) ∣ (Nat.card Fˣ : ℤ) := by
    have h : 2 ^ r ∣ Nat.card Fˣ := by rw [card_units_eq_of_card hF]; exact hdvd
    exact_mod_cast h
  have hqt : ((2 : ℤ) ^ r) ∣ (q : ℤ) - t * t := by
    have h := h2rN.trans hdvd_tq
    have h' : ((2 : ℤ) ^ r) ∣ -(t * t - (q : ℤ)) := dvd_neg.mpr h
    simpa [neg_sub] using h'
  have hx₀t : x₀ ^ t = x₀ ∨ x₀ ^ t = x₀⁻¹ := by
    simpa [ht'] using hfix'
  have hdvd_t : ((2 : ℤ) ^ (r - 1)) ∣ t - 1 ∨ ((2 : ℤ) ^ (r - 1)) ∣ t + 1 := by
    rcases hx₀t with h | h
    · left
      have h1 : x₀ ^ (t - 1) = 1 := by
        rw [zpow_sub, h, zpow_one, mul_inv_cancel]
      have hd := orderOf_dvd_iff_zpow_eq_one.mpr h1
      rwa [hx₀] at hd
    · right
      have h1 : x₀ ^ (t + 1) = 1 := by
        rw [zpow_add, h, zpow_one, inv_mul_cancel]
      have hd := orderOf_dvd_iff_zpow_eq_one.mpr h1
      rwa [hx₀] at hd
  have h2rt : ((2 : ℤ) ^ r) ∣ t * t - 1 := by
    rcases hdvd_t with h | h
    · exact pow_two_dvd_sq_sub_one_of_dvd_sub (by omega : 2 ≤ r) h
    · exact pow_two_dvd_sq_sub_one_of_dvd_add (by omega : 2 ≤ r) h
  have hq1 : ((2 : ℤ) ^ r) ∣ (q : ℤ) - 1 := by
    have := dvd_add hqt h2rt
    convert this using 1
    ring
  have h2q1 : (2 : ℤ) ∣ (q : ℤ) + 1 := by
    obtain ⟨s, hs⟩ := hqodd
    refine ⟨(s : ℤ) + 1, ?_⟩
    have : (q : ℤ) = 2 * (s : ℤ) + 1 := by exact_mod_cast hs
    omega
  have hmain : ((2 : ℤ) ^ (r + 1)) ∣ ((p ^ f - 1 : ℕ) : ℤ) := by
    have hmul : ((2 : ℤ) ^ r * 2) ∣ ((q : ℤ) - 1) * ((q : ℤ) + 1) := mul_dvd_mul hq1 h2q1
    have heq : ((2 : ℤ) ^ (r + 1)) = (2 : ℤ) ^ r * 2 := by rw [pow_succ]
    have hcast : ((q * q - 1 : ℕ) : ℤ) = ((q : ℤ) - 1) * ((q : ℤ) + 1) := by
      have h1 : 1 ≤ q * q := by rw [hqq]; exact Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
      rw [Nat.cast_sub h1, Nat.cast_mul]
      ring
    have hpf : ((p ^ f - 1 : ℕ) : ℤ) = ((q : ℤ) - 1) * ((q : ℤ) + 1) := by
      rw [← hqq]; exact hcast
    rw [heq, hpf]
    exact hmul
  exact harith (Int.natCast_dvd_natCast.mp (by simpa using hmain))

end AutFix

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
