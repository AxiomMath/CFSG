module

public import CFSG.ClassicalInvolution.Q3.TL4ExitDichA

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

open CFSG.LocalAnalysis.ComponentInitial (finite_field_automorphism_fixed_field_cardinality)

variable {K : Type} [Field K]

theorem frob_pow_apply {p : ℕ} {σ : K ≃+* K} (hσ : ∀ a, σ a = a ^ p) (n : ℕ) (x : K) :
    (σ ^ n) x = x ^ (p ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', RingAut.mul_apply, ih, hσ, ← pow_mul, pow_succ' p n, mul_comm]

theorem exists_involution_frob {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) {ρ : K ≃+* K} (hρ : ρ * ρ = 1) (hρ1 : ρ ≠ 1) :
    ∃ q₁ : ℕ, Odd q₁ ∧ q₁ * q₁ = p ^ f ∧ ∀ x : K, ρ x = x ^ q₁ := by
  obtain ⟨σ, hσ, hσord, htop, hcard, -⟩ := finite_field_automorphism_fixed_field_cardinality hp hf hK
  have hfin : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  haveI : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ, htop⟩
  have hρ2 : orderOf ρ = 2 := orderOf_eq_prime (by rw [sq]; exact hρ) hρ1
  have h2f : 2 ∣ f := hcard ▸ hρ2 ▸ orderOf_dvd_natCard ρ
  obtain ⟨g, hg⟩ := h2f
  have hg0 : 0 < g := by omega
  have hσg : orderOf (σ ^ g) = 2 := by
    rw [orderOf_pow' σ hg0.ne', hσord, hg]
    have : Nat.gcd (2 * g) g = g := Nat.gcd_mul_left_left 2 g
    rw [this]
    exact Nat.mul_div_cancel 2 hg0
  have hσg2 : (σ ^ g) ^ 2 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hσg]
  have hσg1 : σ ^ g ≠ 1 := fun h => by rw [h, orderOf_one] at hσg; omega
  have heq : ρ = σ ^ g :=
    CFSG.ClassicalInvolution.Q3.TL4.MF163.eq_of_sq_eq_one_of_isCyclic (by rw [sq]; exact hρ) hσg2
      hρ1 hσg1
  refine ⟨p ^ g, (hp.odd_of_ne_two hp2).pow, ?_, fun x => ?_⟩
  · rw [← pow_add, hg]
    congr 1
    omega
  · rw [heq, frob_pow_apply hσ]

theorem pow_apply_eq_self {σ : K ≃+* K} {x : K} (h : σ x = x) (n : ℕ) : (σ ^ n) x = x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', RingAut.mul_apply, ih, h]

theorem fieldAut_eq_one {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) {l : Kˣ} {k : ℕ} (hlord : orderOf l = 2 ^ k)
    (hmax : ¬ 2 ^ (k + 1) ∣ Nat.card Kˣ) {τ : K ≃+* K} {s : ℕ} (hτ : τ ^ 2 ^ s = 1)
    (hl : τ (l : K) = l ∨ τ (l : K) = ((l⁻¹ : Kˣ) : K)) : τ = 1 := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  by_contra hτ1
  obtain ⟨t, -, ht⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hτ)
  have ht1 : 1 ≤ t := by
    by_contra h0
    have : t = 0 := by omega
    rw [this, pow_zero, orderOf_eq_one_iff] at ht
    exact hτ1 ht
  have hρ2 : τ ^ 2 ^ (t - 1) * τ ^ 2 ^ (t - 1) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel ht1, ← ht]
    exact pow_orderOf_eq_one τ
  have hρ1 : τ ^ 2 ^ (t - 1) ≠ 1 := by
    intro h
    have h1 : orderOf τ ∣ 2 ^ (t - 1) := orderOf_dvd_of_pow_eq_one h
    rw [ht] at h1
    have h2 := Nat.le_of_dvd (by positivity) h1
    have h3 : 2 ^ (t - 1) < 2 ^ t := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hρl : (τ ^ 2 ^ (t - 1)) (l : K) = l ∨ (τ ^ 2 ^ (t - 1)) (l : K) = ((l⁻¹ : Kˣ) : K) := by
    rcases Nat.lt_or_ge 1 t with h | h
    · left
      have hτ2 : (τ ^ 2) (l : K) = l := by
        rw [pow_two, RingAut.mul_apply]
        rcases hl with h1 | h1
        · rw [h1, h1]
        · rw [h1, Units.val_inv_eq_inv_val, map_inv₀, h1, Units.val_inv_eq_inv_val, inv_inv]
      have hexp : 2 ^ (t - 1) = 2 * 2 ^ (t - 2) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [hexp, pow_mul]
      exact pow_apply_eq_self hτ2 _
    · have ht1' : t = 1 := le_antisymm h ht1
      subst ht1'
      simpa using hl
  obtain ⟨q₁, hq₁odd, hq₁sq, hq₁⟩ := exists_involution_frob hp hp2 hf hK hρ2 hρ1
  have hq0 : 1 ≤ q₁ := hq₁odd.pos
  have hcard : Nat.card Kˣ = (q₁ - 1) * (q₁ + 1) := by
    rw [Nat.card_units, hK, ← hq₁sq]
    obtain ⟨m, rfl⟩ : ∃ m, q₁ = m + 1 := ⟨q₁ - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  have h2a : 2 ∣ q₁ - 1 := by
    obtain ⟨m, hm⟩ := hq₁odd
    omega
  have h2b : 2 ∣ q₁ + 1 := by
    obtain ⟨m, hm⟩ := hq₁odd
    omega
  have hlq : ∀ u : Kˣ, (u : K) = (l : K) ^ q₁ → u = l ^ q₁ := fun u hu =>
    Units.ext (by rw [hu, Units.val_pow_eq_pow_val])
  rcases hρl with h | h
  · apply hmax
    have hl1 : l ^ q₁ = l := hlq l (by rw [← hq₁]; exact h.symm) |>.symm
    have hl2 : l ^ (q₁ - 1) = 1 := by
      have : l ^ (q₁ - 1) * l = l := by
        rw [← pow_succ, Nat.sub_add_cancel hq0]
        exact hl1
      simpa using this
    have h3 : 2 ^ k ∣ q₁ - 1 := hlord ▸ orderOf_dvd_of_pow_eq_one hl2
    rw [hcard, pow_succ]
    exact Nat.mul_dvd_mul h3 h2b
  · apply hmax
    have hl1 : l ^ q₁ = l⁻¹ := hlq (l⁻¹) (by rw [← hq₁]; exact h.symm) |>.symm
    have hl2 : l ^ (q₁ + 1) = 1 := by rw [pow_succ, hl1, inv_mul_cancel]
    have h3 : 2 ^ k ∣ q₁ + 1 := hlord ▸ orderOf_dvd_of_pow_eq_one hl2
    rw [hcard, pow_succ, mul_comm (q₁ - 1)]
    exact Nat.mul_dvd_mul h3 h2a

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
