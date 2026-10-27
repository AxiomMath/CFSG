module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L2VKap

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

open CFSG CFSG.GorensteinWalter

variable {K : Type} [Field K]

theorem sq_eq_one_of_comm [Finite K] (h2 : (2 : K) ≠ 0) {B : PGammaL2 K}
    (hB : B * tor (-1) = tor (-1) * B) {α : Kˣ} {t : ℕ} (ht : 3 ≤ t) (hα : orderOf α = 2 ^ t)
    (hBα : B * tor α * B⁻¹ = tor α⁻¹) {c : Kˣ} {a : ℕ} (hca : c ^ 2 ^ a = 1)
    (hBc : B * tor c * B⁻¹ = tor c) : c = 1 ∨ c = -1 := by
  obtain ⟨m, -, hm⟩ := exists_pow_conj h2 hB
  have h1 : α ^ m = α⁻¹ := tor_injective (by rw [← hm, hBα, map_inv])
  have h2' : c ^ m = c := tor_injective (by rw [← hm, hBc])
  have h3 : α ^ (m + 1) = 1 := by rw [pow_succ, h1, inv_mul_cancel]
  have h4 : 2 ^ t ∣ m + 1 := hα ▸ orderOf_dvd_of_pow_eq_one h3
  have h5 : 8 ∣ m + 1 := by
    have : (8 : ℕ) ∣ 2 ^ t := by
      have h8 : (2 : ℕ) ^ 3 ∣ 2 ^ t := pow_dvd_pow 2 ht
      simpa using h8
    exact this.trans h4
  obtain ⟨q, hq⟩ := h5
  have hm1 : m = 8 * q - 1 := by omega
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · omega
    · exact h
  have h6 : c ^ (m - 1) = 1 := by
    have : c ^ (m - 1) * c = c := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      exact h2'
    simpa using this
  have h7 : c ^ Nat.gcd (2 ^ a) (m - 1) = 1 := pow_gcd_eq_one.mpr ⟨hca, h6⟩
  have h8 : Nat.gcd (2 ^ a) (m - 1) ∣ 2 := by
    obtain ⟨i, hi, hgi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Nat.gcd_dvd_left (2 ^ a) (m - 1))
    rw [hgi]
    by_cases hi1 : i ≤ 1
    · simpa using pow_dvd_pow 2 hi1
    · exfalso
      have h4' : 2 ^ 2 ∣ m - 1 := by
        have : 2 ^ 2 ∣ 2 ^ i := pow_dvd_pow 2 (by omega)
        exact this.trans (hgi ▸ Nat.gcd_dvd_right (2 ^ a) (m - 1))
      omega
  have h9 : c ^ 2 = 1 := by
    obtain ⟨e, he⟩ := h8
    rw [he, pow_mul, h7, one_pow]
  have h10 : ((c : Kˣ) : K) * (c : K) = 1 := by
    have := congrArg Units.val h9
    simpa [sq] using this
  rcases mul_self_eq_one_iff.mp h10 with h | h
  · left; exact Units.ext h
  · right; exact Units.ext (by simpa using h)

theorem rightHom_tor (a : Kˣ) :
    (SemidirectProduct.rightHom : PGammaL2 K →* (K ≃+* K)) (tor a) = 1 := by
  rw [tor_apply]; exact SemidirectProduct.rightHom_inl _

theorem rightHom_wref :
    (SemidirectProduct.rightHom : PGammaL2 K →* (K ≃+* K)) wref = 1 := by
  rw [wref]; exact SemidirectProduct.rightHom_inl _

theorem core_false [Finite K] (h2 : (2 : K) ≠ 0) {k : ℕ} (hk : 2 ≤ k)
    {u : PGammaL2 K} (hu1 : u * tor (-1) = tor (-1) * u) (hun : u ^ 2 ^ k = tor (-1))
    {B : PGammaL2 K} (hB : B * tor (-1) = tor (-1) * B) (hBu : B * u = u * B)
    {α : Kˣ} {t : ℕ} (ht : 3 ≤ t) (hα : orderOf α = 2 ^ t) (hBα : B * tor α * B⁻¹ = tor α⁻¹)
    {U N : Subgroup (PGammaL2 K)} (hNodd : Odd (Nat.card N)) (hNU : N ≤ U) (huU : u ∈ U)
    (hU : ∀ g ∈ U, ∃ n ∈ N, ∃ j : ℤ, g = n * u ^ j)
    (hUZ : ∀ g ∈ U, g * tor (-1) = tor (-1) * g)
    (hρ : ∀ g ∈ U, (tor (-1) * wref) * g * (tor (-1) * wref)⁻¹ ∈ U) : False := by
  classical
  obtain ⟨γ, ε, σ, hε, hu⟩ := exists_decomp h2 hu1
  set μ : PGammaL2 K := wref ^ ε * SemidirectProduct.inr σ with hμ
  have hu' : u = tor γ * μ := by rw [hu, hμ, mul_assoc]
  have hμw : μ * wref = wref * μ := by
    have h1 : (wref : PGammaL2 K) ^ ε * wref = wref * wref ^ ε := (Commute.pow_self (wref : PGammaL2 K) ε).eq
    rw [hμ, mul_assoc, inr_mul_wref, ← mul_assoc, h1, mul_assoc]
  have hμZ : μ * tor (-1) = tor (-1) * μ := by
    have hμ' : μ = (tor γ)⁻¹ * u := by rw [hu', ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hμ', mul_assoc, hu1, ← mul_assoc, ← mul_assoc]
    congr 1
    rw [← map_inv, tor_comm]
  obtain ⟨m, hmodd, hm⟩ := exists_pow_conj h2 hμZ
  have hform := pow_tor_mul hm γ
  have hσk : σ ^ 2 ^ k = 1 := by
    have h1 := congrArg (SemidirectProduct.rightHom : PGammaL2 K →* (K ≃+* K)) hun
    rw [map_pow, hu, map_mul, map_mul, map_pow, rightHom_tor, rightHom_wref, SemidirectProduct.rightHom_inr,
      rightHom_tor] at h1
    simpa using h1
  have hw2 : (wref : PGammaL2 K) ^ 2 = 1 := by rw [sq, wref_mul_wref]
  have hμn : μ ^ 2 ^ k = 1 := by
    have hc : Commute (wref ^ ε : PGammaL2 K) (SemidirectProduct.inr σ) :=
      Commute.pow_left (inr_mul_wref σ).symm ε
    obtain ⟨j, hj⟩ : 2 ∣ ε * 2 ^ k := Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) ε
    rw [hμ, hc.mul_pow, ← pow_mul, hj, pow_mul, hw2, one_pow, ← map_pow, hσk, map_one, mul_one]
  have hS : γ ^ (∑ i ∈ Finset.range (2 ^ k), m ^ i) = -1 := by
    apply tor_injective
    have := hform (2 ^ k)
    rw [← hu', hun, hμn, mul_one] at this
    exact this.symm
  set ρ' : PGammaL2 K := tor (-1) * wref with hρ'
  have hρu : ρ' * u * ρ'⁻¹ = tor γ⁻¹ * μ := by
    have e1 : wref * (tor γ * μ) * wref⁻¹ = tor γ⁻¹ * μ := by
      calc wref * (tor γ * μ) * wref⁻¹ = (wref * tor γ * wref⁻¹) * (wref * μ * wref⁻¹) := by group
        _ = tor γ⁻¹ * μ := by rw [conj_tor_wref, ← hμw, mul_inv_cancel_right]
    have e2 : tor (-1) * (tor γ⁻¹ * μ) * (tor (-1))⁻¹ = tor γ⁻¹ * μ := by
      rw [mul_inv_eq_iff_eq_mul, ← mul_assoc, tor_comm (-1) γ⁻¹, mul_assoc, mul_assoc, hμZ]
    calc ρ' * u * ρ'⁻¹ = tor (-1) * (wref * u * wref⁻¹) * (tor (-1))⁻¹ := by rw [hρ']; group
      _ = _ := by rw [hu', e1, e2]
  have hτ : ρ' * u * ρ'⁻¹ * u⁻¹ = tor (γ⁻¹ * γ⁻¹) := by
    rw [hρu, hu']
    calc tor γ⁻¹ * μ * (tor γ * μ)⁻¹ = tor γ⁻¹ * (μ * μ⁻¹) * (tor γ)⁻¹ := by group
      _ = tor (γ⁻¹ * γ⁻¹) := by rw [mul_inv_cancel, mul_one, ← map_inv, ← map_mul]
  have hτU : tor (γ⁻¹ * γ⁻¹) ∈ U := by
    rw [← hτ]
    exact U.mul_mem (hρ u huU) (U.inv_mem huU)
  set τ : PGammaL2 K := tor (γ⁻¹ * γ⁻¹) with hτdef
  obtain ⟨a, b', hb', hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos τ).ne'
  have hτ2 : (τ ^ b') ^ 2 ^ a = 1 := by
    rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have huk : u ^ 2 ^ (k + 1) = 1 := by
    rw [pow_succ, pow_mul, hun, sq, tor_neg_one_sq]
  obtain ⟨h, hhU, j, hj⟩ := exists_conj_mem_zpowers hNodd hNU huU huk hU (U.pow_mem hτU b') hτ2
  have hhZ : h * tor (-1) = tor (-1) * h := hUZ h hhU
  have hhinvZ : h⁻¹ * tor (-1) = tor (-1) * h⁻¹ := (Commute.inv_left (show Commute h (tor (-1)) from hhZ)).eq
  have hτ₂ : τ ^ b' = tor ((γ⁻¹ * γ⁻¹) ^ b') := by rw [hτdef, map_pow]
  have hujeq : u ^ j = h⁻¹ * (τ ^ b') * h := by rw [hj]; group
  obtain ⟨c, hc⟩ := tor_conj_mem h2 hhinvZ ((γ⁻¹ * γ⁻¹) ^ b')
  rw [inv_inv] at hc
  have hujc : u ^ j = tor c := by rw [hujeq, hτ₂, hc]
  have hca : c ^ 2 ^ a = 1 := by
    apply tor_injective
    have hconj : ∀ x : PGammaL2 K, (h⁻¹ * x * h) ^ 2 ^ a = h⁻¹ * x ^ 2 ^ a * h := fun x => by
      simpa using conj_pow (a := h⁻¹) (b := x) (i := 2 ^ a)
    rw [map_pow, ← hujc, hujeq, hconj, hτ2, mul_one, inv_mul_cancel, map_one]
  have hBuj : B * u ^ j = u ^ j * B := (Commute.zpow_right (show Commute B u from hBu) j).eq
  have hBc : B * tor c * B⁻¹ = tor c := by
    rw [← hujc, mul_inv_eq_iff_eq_mul]; exact hBuj
  have hc1 := sq_eq_one_of_comm h2 hB ht hα hBα hca hBc
  have hτc : τ ^ b' = tor c := by
    rw [hj, hujc]
    rcases hc1 with rfl | rfl
    · simp
    · exact mul_inv_eq_iff_eq_mul.mpr hhZ
  have hcc : (γ⁻¹ * γ⁻¹) ^ b' = c := by
    apply tor_injective
    rw [← hτc, hτ₂]
  have hc2 : c ^ 2 = 1 := by rcases hc1 with rfl | rfl <;> simp
  have hγ4 : γ ^ (4 * b') = 1 := by
    have e : ((γ⁻¹ * γ⁻¹) ^ b') ^ 2 = (γ⁻¹) ^ (4 * b') := by
      rw [← sq, ← pow_mul, ← pow_mul]; congr 1; ring
    have : (γ ^ (4 * b'))⁻¹ = 1 := by rw [← inv_pow, ← e, hcc, hc2]
    exact inv_eq_one.mp this
  have h4S : 4 ∣ ∑ i ∈ Finset.range (2 ^ k), m ^ i :=
    (show (4 : ℕ) ∣ 2 ^ k from (pow_dvd_pow 2 hk : (2 : ℕ) ^ 2 ∣ 2 ^ k)).trans (two_pow_dvd_sum_pow hmodd k)
  obtain ⟨S4, hS4⟩ := h4S
  have h5 : (γ ^ (∑ i ∈ Finset.range (2 ^ k), m ^ i)) ^ b' = 1 := by
    rw [hS4, ← pow_mul, show 4 * S4 * b' = (4 * b') * S4 by ring, pow_mul, hγ4, one_pow]
  rw [hS, Odd.neg_one_pow hb'] at h5
  have h6 : ((-1 : Kˣ) : K) = ((1 : Kˣ) : K) := congrArg Units.val h5
  simp only [Units.val_neg, Units.val_one] at h6
  exact h2 (by linear_combination -h6)

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
