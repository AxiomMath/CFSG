module

public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving

variable {G : Type*} [Group G]

theorem eq_one_of_cube_of_coprime [Finite G] {N : Subgroup G} (hN : Nat.Coprime 3 (Nat.card N))
    {n : G} (hn : n ∈ N) (h : n * n * n = 1) : n = 1 := by
  have h3 : orderOf n ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [pow_three', h])
  have hc : orderOf n ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨n, hn⟩ : N)
    rwa [Subgroup.orderOf_mk] at this
  have h1 : orderOf n ∣ Nat.gcd 3 (Nat.card N) := Nat.dvd_gcd h3 hc
  rw [hN.gcd_eq_one] at h1
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)

theorem eq_of_sq_eq_one_of_cube {x e : G} (h : x * e * (x * e) * (x * e) = 1)
    (h2 : x * e * (x * e) = 1) : x * e = e * x := by
  have h1 : x * e = 1 := by
    calc x * e = x * e * (x * e) * (x * e) * ((x * e) * (x * e))⁻¹ := by group
      _ = 1 := by rw [h, h2, inv_one, one_mul]
  have he : e = x⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [he, mul_inv_cancel, inv_mul_cancel]

theorem commute_of_sepThree {H : Type*} [Group H] [Finite G] (ι : G →* H)
    (hι : Function.Injective ι) {N : Subgroup G} (hN : Nat.Coprime 3 (Nat.card N)) {D₀ : Set H}
    (h2 : ∀ d ∈ D₀, d * d = 1)
    (h3 : ∀ d ∈ D₀, ∀ e ∈ D₀, d * e ≠ e * d → d * e * (d * e) * (d * e) = 1)
    (hnorm : ∀ d ∈ D₀, ∀ n ∈ N, ∃ m ∈ N, ι m = d * ι n * d⁻¹)
    (hstab : ∀ d ∈ D₀, ∀ n ∈ N, (ι n)⁻¹ * d * ι n ∈ D₀)
    (hsep : ∀ d ∈ D₀, ∀ d' ∈ D₀, d ≠ d' → d * d' = d' * d →
      ∃ e ∈ D₀, (e * d = d * e ∧ e * d' ≠ d' * e) ∨ (e * d ≠ d * e ∧ e * d' = d' * e)) :
    ∀ n ∈ N, ∀ d ∈ D₀, ι n * d = d * ι n := by
  have hcube : ∀ m ∈ N, ι m * ι m * ι m = 1 → ι m = 1 := by
    intro m hm h
    rw [← map_mul, ← map_mul, ← map_one ι] at h
    rw [eq_one_of_cube_of_coprime hN hm (hι h), map_one]
  intro n hn d hd
  set d' := (ι n)⁻¹ * d * ι n with hd'
  have hd'D : d' ∈ D₀ := hstab d hd n hn
  have hdd : d * d = 1 := h2 d hd
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  have hdd' : d' * d' = 1 := h2 d' hd'D
  obtain ⟨m₁, hm₁, he₁⟩ := hnorm d hd n⁻¹ (N.inv_mem hn)
  have hz : d * d' = ι (m₁ * n) := by
    rw [map_mul, he₁, hd', map_inv, hdi]
    group
  have hzN : m₁ * n ∈ N := N.mul_mem hm₁ hn
  have hcomm : d * d' = d' * d := by
    by_contra hne
    have h1 := hcube _ hzN (by rw [← hz]; exact h3 d hd d' hd'D hne)
    rw [← hz] at h1
    apply hne
    have : d' = d⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this, mul_inv_cancel, inv_mul_cancel]
  by_cases heq : d = d'
  · have h' : (ι n)⁻¹ * d * ι n = d := heq.symm
    calc ι n * d = ι n * ((ι n)⁻¹ * d * ι n) := by rw [h']
      _ = d * ι n := by group
  · exfalso
    obtain ⟨e, he, hcase⟩ := hsep d hd d' hd'D heq hcomm
    have hee : e * e = 1 := h2 e he
    have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
    obtain ⟨m₂, hm₂, he₂⟩ := hnorm e he (m₁ * n) hzN
    have hw : d * d' * (e * (d * d') * e) = ι (m₁ * n * m₂) := by
      rw [map_mul ι (m₁ * n) m₂, he₂, ← hz, hei]
    have hwN : m₁ * n * m₂ ∈ N := N.mul_mem hzN hm₂
    rcases hcase with ⟨hed, hed'⟩ | ⟨hed, hed'⟩
    ·
      have e1 : d * d' * (e * (d * d') * e) = d' * e * (d' * e) := by
        calc d * d' * (e * (d * d') * e) = d * d' * ((e * d) * d' * e) := by
              simp only [mul_assoc]
          _ = d * d' * ((d * e) * d' * e) := by rw [hed]
          _ = d * (d' * d) * e * d' * e := by simp only [mul_assoc]
          _ = d * (d * d') * e * d' * e := by rw [hcomm]
          _ = (d * d) * d' * e * d' * e := by simp only [mul_assoc]
          _ = d' * e * (d' * e) := by rw [hdd]; simp only [one_mul, mul_assoc]
      have hc3 : d' * e * (d' * e) * (d' * e) = 1 := h3 d' hd'D e he fun h => hed' h.symm
      have hw3 : ι (m₁ * n * m₂) * ι (m₁ * n * m₂) * ι (m₁ * n * m₂) = 1 := by
        rw [← hw, e1]
        calc d' * e * (d' * e) * (d' * e * (d' * e)) * (d' * e * (d' * e))
            = (d' * e * (d' * e) * (d' * e)) * (d' * e * (d' * e) * (d' * e)) := by group
          _ = 1 := by rw [hc3, one_mul]
      have h1 := hcube _ hwN hw3
      rw [← hw, e1] at h1
      exact hed' (eq_of_sq_eq_one_of_cube hc3 h1).symm
    ·
      have e1 : d * d' * (e * (d * d') * e) = d * e * (d * e) := by
        calc d * d' * (e * (d * d') * e) = d * (d' * e) * d * d' * e := by
              simp only [mul_assoc]
          _ = d * (e * d') * d * d' * e := by rw [hed']
          _ = d * e * (d' * d) * d' * e := by simp only [mul_assoc]
          _ = d * e * (d * d') * d' * e := by rw [hcomm]
          _ = d * e * d * (d' * d') * e := by simp only [mul_assoc]
          _ = d * e * (d * e) := by rw [hdd']; simp only [mul_one, mul_assoc]
      have hc3 : d * e * (d * e) * (d * e) = 1 := h3 d hd e he fun h => hed h.symm
      have hw3 : ι (m₁ * n * m₂) * ι (m₁ * n * m₂) * ι (m₁ * n * m₂) = 1 := by
        rw [← hw, e1]
        calc d * e * (d * e) * (d * e * (d * e)) * (d * e * (d * e))
            = (d * e * (d * e) * (d * e)) * (d * e * (d * e) * (d * e)) := by group
          _ = 1 := by rw [hc3, one_mul]
      have h1 := hcube _ hwN hw3
      rw [← hw, e1] at h1
      exact hed (eq_of_sq_eq_one_of_cube hc3 h1).symm

theorem three_dvd_orderOf_of_smul_cycle {X : Type*} [MulAction G X] (g : G) (p : X) {L : ℕ}
    (hL : 3 ∣ L) (h1 : g ^ L • p = p) (h2 : g ^ (L / 3) • p ≠ p) : 3 ∣ orderOf g := by
  have hmL : Function.minimalPeriod (g • ·) p ∣ L :=
    MulAction.pow_smul_eq_iff_minimalPeriod_dvd.1 h1
  have hmL3 : ¬ Function.minimalPeriod (g • ·) p ∣ L / 3 := fun h =>
    h2 (MulAction.pow_smul_eq_iff_minimalPeriod_dvd.2 h)
  have hm3 : 3 ∣ Function.minimalPeriod (g • ·) p := by
    by_contra h3
    have hcop : Nat.Coprime (Function.minimalPeriod (g • ·) p) 3 :=
      Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)
    obtain ⟨k, hk⟩ := hL
    apply hmL3
    rw [hk, Nat.mul_div_cancel_left _ (by norm_num)]
    exact hcop.dvd_of_dvd_mul_left (hk ▸ hmL)
  have hmo : Function.minimalPeriod (g • ·) p ∣ orderOf g :=
    MulAction.pow_smul_eq_iff_minimalPeriod_dvd.1 (by rw [pow_orderOf_eq_one, one_smul])
  exact hm3.trans hmo

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
