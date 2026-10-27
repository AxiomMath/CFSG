module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87QuotTools
public import CFSG.Sporadic.Schreier.J1OddCore
public import CFSG.Sporadic.Schreier.J1Outer

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.Blueprint
open scoped commutatorElement

theorem noQuotCfg_J1
    {Y : Type} [Group Y] [Finite Y]
    (hY : NativeSporadic.IsSporadic Y .J1) {p : ℕ} {α : MulAut Y} {Xh : Subgroup Y}
    (h : QuotCfg p α Xh) : False := by
  classical
  obtain ⟨e⟩ := hY
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card Y = 175560 := by
    rw [Nat.card_congr e.toEquiv]; exact CFSG.Sporadic.J1.card_J1
  obtain ⟨t, hαt⟩ := exists_conj_of_equiv e (CFSG.Sporadic.Schreier.at_j1_schreier.2.1) α
  have hZ := center_eq_bot_of_simple h.simple h.nonab
  have ht2 : t * t = 1 := by
    apply sq_eq_one_of_conj_invol hZ
    intro s
    have := h.invol s
    rwa [hαt] at this
  have ht1 : t ≠ 1 := by
    rintro rfl
    apply h.not_fixed
    intro x _
    rw [hαt]
    simp
  have hto : orderOf t = 2 := orderOf_eq_prime (by rwa [pow_two]) ht1
  have hfix : ∀ y, α y = y ↔ y ∈ centralizer ({t} : Set Y) := by
    intro y
    rw [Subgroup.mem_centralizer_singleton_iff, hαt, MulAut.conj_apply]
    constructor
    · intro h1
      calc y * t = (t * y * t⁻¹) * t := by rw [h1]
        _ = t * y := by group
    · intro h1
      calc t * y * t⁻¹ = (y * t) * t⁻¹ := by rw [h1]
        _ = y := by group
  have hdata : ∀ u : Y, orderOf u = 2 →
      Nat.card ↥(centralizer ({u} : Set Y)) = 120 ∧ CFSG.oddCore ↥(centralizer ({u} : Set Y)) = ⊥ :=
    fun u hu => by
      obtain ⟨h1, -, -, h4⟩ :=
        CFSG.Sporadic.Schreier.ctugs_j1_involution_centralizer_odd_core_free ⟨e⟩ u hu
      exact ⟨h1, h4⟩
  obtain ⟨hCt, hOt⟩ := hdata t hto
  have hpdvd : p ∣ 175560 := hcard ▸ h.dvd_card
  have hp' : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 19 := by
    have e1 : (175560 : ℕ) = 2 ^ 3 * 3 * 5 * 7 * 11 * 19 := by norm_num
    rw [e1] at hpdvd
    have hq : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hd =>
      (Nat.prime_dvd_prime_iff_eq hp hq).mp hd
    rcases (Nat.Prime.dvd_mul hp).mp hpdvd with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
      · rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
        · rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
          · rcases (Nat.Prime.dvd_mul hp).mp h4 with h5 | h5
            · exact absurd (hq 2 Nat.prime_two (hp.dvd_of_dvd_pow h5)) h.odd
            · exact Or.inl (hq 3 Nat.prime_three h5)
          · exact Or.inr (Or.inl (hq 5 Nat.prime_five h4))
        · exact Or.inr (Or.inr (Or.inl (hq 7 (by norm_num) h3)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (hq 11 (by norm_num) h2))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (hq 19 (by norm_num) h1))))
  have hsyl : ∀ Q : Subgroup Y, IsPGroup p ↥Q → Nat.card ↥Q ≤ p := by
    intro Q hQ
    obtain ⟨k, hk⟩ := hQ.exists_card_eq
    have hdvd : p ^ k ∣ 175560 := hk ▸ (hcard ▸ Subgroup.card_subgroup_dvd_card Q)
    rw [hk]
    by_contra hlt
    have hlt' : p < p ^ k := not_le.mp hlt
    have hk2 : 2 ≤ k := by
      by_contra hk2
      have h1 : k ≤ 1 := by omega
      have h2 : p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos h1
      rw [pow_one] at h2
      omega
    have h2 : p ^ 2 ∣ 175560 := (pow_dvd_pow p hk2).trans hdvd
    rcases hp' with rfl | rfl | rfl | rfl | rfl <;> norm_num at h2
  rcases hp' with rfl | rfl | hp7
  ·
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hCt]; norm_num)
    exact h.false_of_sylow_row hsyl (Or.inl ⟨(s : Y), (hfix _).2 s.2, by
      rw [Subgroup.orderOf_coe]; exact hs⟩)
  ·
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 5 (by rw [hCt]; norm_num)
    exact h.false_of_sylow_row hsyl (Or.inl ⟨(s : Y), (hfix _).2 s.2, by
      rw [Subgroup.orderOf_coe]; exact hs⟩)
  ·
    obtain ⟨u, -, hu2, hu1, huC⟩ := exists_involution_in_oddClosure (centralizer ({t} : Set Y)) hOt
      (q := 3) Nat.prime_three (by norm_num) (by rw [hCt]; norm_num)
    have hset : {y : Y | y ∈ centralizer ({t} : Set Y) ∧ Odd (orderOf y)} =
        {y : Y | α y = y ∧ Odd (orderOf y)} := by
      ext y
      exact and_congr_left' (hfix y).symm
    rw [hset] at huC
    have huo : orderOf u = 2 := orderOf_eq_prime (by rwa [pow_two]) hu1
    obtain ⟨hCu, -⟩ := hdata u huo
    refine h.false_of_sylow_row hsyl (Or.inr ⟨u, hu2, hu1, huC, ?_⟩)
    rw [hCu]
    rcases hp7 with rfl | rfl | rfl <;> norm_num

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
