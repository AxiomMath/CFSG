module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10ABasS

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzR10A

variable {G : Type} [Group G] {t tau lam rho : G} {Z E W Q R T P : Subgroup G}

private lemma fzrAux_conj_pow {rho a b : G} (h : rho * a * rho⁻¹ = b) (x : ℕ) :
    rho * a ^ x * rho⁻¹ = b ^ x := by
  induction x with
  | zero => simp
  | succ x ih =>
      rw [pow_succ, pow_succ]
      calc rho * (a ^ x * a) * rho⁻¹
          = (rho * a ^ x * rho⁻¹) * (rho * a * rho⁻¹) := by group
        _ = b ^ x * b := by rw [ih, h]

private lemma fzrAux_inv_pow_mod (a : G) (ha8 : a ^ 8 = 1) {y : ℕ} (hy : y < 8) :
    (a ^ y)⁻¹ = a ^ ((7 * y) % 8) := by
  have hexp : (-(y : ℤ)) % (((8 : ℕ) : ℤ)) = ((7 * y) % 8 : ℕ) := by
    interval_cases y <;> norm_num
  have h1 : (a ^ y)⁻¹ = a ^ (-(y : ℤ)) := by rw [zpow_neg, zpow_natCast]
  rw [h1, zpow_eq_zpow_emod' (-(y : ℤ)) ha8, hexp, zpow_natCast]

private lemma fzrAux_mul_inv_pow_mod (b : G) (hb8 : b ^ 8 = 1) {x y : ℕ}
    (hx : x < 8) (hy : y < 8) :
    b ^ x * (b ^ y)⁻¹ = b ^ ((x + 7 * y) % 8) := by
  have hexp : ((x : ℤ) + -(y : ℤ)) % (((8 : ℕ) : ℤ)) = ((x + 7 * y) % 8 : ℕ) := by
    interval_cases x <;> interval_cases y <;> norm_num
  have h1 : b ^ x * (b ^ y)⁻¹ = b ^ ((x : ℤ) + -(y : ℤ)) := by
    rw [← zpow_natCast b x, ← zpow_natCast b y, ← zpow_neg, ← zpow_add]
  rw [h1, zpow_eq_zpow_emod' ((x : ℤ) + -(y : ℤ)) hb8, hexp, zpow_natCast]

private lemma fzrAux_rho0_ap (n : ℕ) :
    rho0.ap n = (7 * (n / 8 % 8)) % 8 + 8 * ((n % 8 + 7 * (n / 8 % 8)) % 8) := by
  simp [Mat.ap, rho0]

private lemma fzrAux_rho0_ap_lo (n : ℕ) :
    rho0.ap n % 8 = (7 * (n / 8 % 8)) % 8 := by
  rw [fzrAux_rho0_ap, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))]

private lemma fzrAux_rho0_ap_hi (n : ℕ) :
    rho0.ap n / 8 % 8 = (n % 8 + 7 * (n / 8 % 8)) % 8 := by
  rw [fzrAux_rho0_ap, Nat.add_mul_div_left _ _ (by norm_num : 0 < 8),
    Nat.div_eq_of_lt (Nat.mod_lt _ (by norm_num)), Nat.zero_add,
    Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))]

private lemma fzrAux_act {a b : G} (ha8 : a ^ 8 = 1) (hb8 : b ^ 8 = 1)
    (hab : a * b = b * a) (hσa : fzrASig rho a = b)
    (hσb : fzrASig rho b = (a * b)⁻¹) : FzR10AAct a b rho rho0 := by
  have hab_inv : Commute b⁻¹ a⁻¹ := by
    show b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹
    rw [show b⁻¹ * a⁻¹ = (a * b)⁻¹ by rw [mul_inv_rev],
      show a⁻¹ * b⁻¹ = (b * a)⁻¹ by rw [mul_inv_rev], hab]
  intro n hn
  have hx : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hy : n / 8 % 8 < 8 := Nat.mod_lt _ (by norm_num)
  calc rho * fzrAElt a b n * rho⁻¹
      = (rho * a ^ (n % 8) * rho⁻¹) * (rho * b ^ (n / 8 % 8) * rho⁻¹) := by
        rw [fzrAElt]; group
    _ = b ^ (n % 8) * ((a * b)⁻¹) ^ (n / 8 % 8) := by
        rw [fzrAux_conj_pow hσa (n % 8), fzrAux_conj_pow hσb (n / 8 % 8)]
    _ = b ^ (n % 8) * ((b⁻¹ * a⁻¹) ^ (n / 8 % 8)) := by rw [mul_inv_rev]
    _ = b ^ (n % 8) * ((b⁻¹) ^ (n / 8 % 8) * (a⁻¹) ^ (n / 8 % 8)) := by
        rw [Commute.mul_pow hab_inv (n / 8 % 8)]
    _ = b ^ (n % 8) * ((b ^ (n / 8 % 8))⁻¹ * (a ^ (n / 8 % 8))⁻¹) := by
        rw [inv_pow, inv_pow]
    _ = (b ^ (n % 8) * (b ^ (n / 8 % 8))⁻¹) * (a ^ (n / 8 % 8))⁻¹ := by group
    _ = a ^ ((7 * (n / 8 % 8)) % 8) * b ^ ((n % 8 + 7 * (n / 8 % 8)) % 8) := by
        rw [fzrAux_mul_inv_pow_mod b hb8 hx hy, fzrAux_inv_pow_mod a ha8 hy,
          (Commute.pow_pow hab _ _).eq.symm]
    _ = fzrAElt a b (rho0.ap n) := by
        rw [fzrAElt, fzrAux_rho0_ap_lo, fzrAux_rho0_ap_hi]

theorem fzr_a_basis (hs : FzStr t tau lam rho Z E W Q R T) (hpf : FzPFacts t tau rho E W Q T P)
    (h8 : FzZ8 Z E P) : ∃ a b : G, FzR10ABasis P a b ∧ FzR10AAct a b rho rho0 := by
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := h8.comm
  obtain ⟨a, haP, haE⟩ := fzr_a_exists_notE hs hpf
  let b : G := fzrASig rho a
  have hσa : fzrASig rho a = b := rfl
  have hbP : b ∈ P := hpf.nrm_P_rho a haP
  have hbE : b ∉ E := fzr_a_b_notE hs haE hσa
  have hab : a * b = b * a := hcomm a haP b hbP
  have hσb : fzrASig rho b = (a * b)⁻¹ := fzr_a_sig_b hs hpf h8 haP hσa
  have habE : a * b ∉ E := fzr_a_ab_notE hs hpf h8 haP haE hσa
  have haibE : a⁻¹ * b ∉ E := fzr_a_haib_notE hs hpf h8 hcomm haP hbP haE hσa
  have hstepA := fzr_a_stepA hcomm hpf hs h8 haP hbP haE hbE habE haibE
  have hspan := fzr_a_span hs hpf hcomm haP hbP hab hstepA
  have ha8 : a ^ 8 = 1 := fzr_a_pow8 hs hpf haP
  have hb8 : b ^ 8 = 1 := fzr_a_pow8 hs hpf hbP
  have hinj := fzr_a_inj_of_span hpf haP hbP hspan
  exact ⟨a, b, ⟨haP, hbP, ha8, hb8, hab, hspan, hinj⟩,
    fzrAux_act ha8 hb8 hab hσa hσb⟩

end CFSG.OddStandard.SmallF3.FritzII
