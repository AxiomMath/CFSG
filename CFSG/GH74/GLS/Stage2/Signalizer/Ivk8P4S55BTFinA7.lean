module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinGlue
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8AltY

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS FinGen FinGlue
open scoped Nat

namespace FinAlt

theorem card_centralizer_of_prime {n : ℕ} {σ : Perm (Fin n)} {p : ℕ} (hp : p.Prime)
    (hσ : orderOf σ = p) : ∃ k : ℕ, 1 ≤ k ∧ σ.support.card = k * p ∧ k * p ≤ n ∧
      Nat.card ↥(centralizer ({σ} : Set (Perm (Fin n)))) = (n - k * p)! * p ^ k * k ! := by
  obtain ⟨m, hm⟩ := cycleType_prime_order (σ := σ) (by rw [hσ]; exact hp)
  rw [hσ] at hm
  refine ⟨m + 1, by omega, ?_, ?_, ?_⟩
  · rw [← sum_cycleType, hm, Multiset.sum_replicate, smul_eq_mul]
  · have h := sum_cycleType_le σ
    rw [hm, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at h
    exact h
  · rw [nat_card_centralizer, hm, Multiset.sum_replicate, smul_eq_mul, Multiset.prod_replicate,
      Fintype.card_fin]
    simp only [Multiset.toFinset_replicate, show m + 1 ≠ 0 by omega, ↓reduceIte,
      Finset.prod_singleton, Multiset.count_replicate_self]

theorem le_of_pow_dvd {n p k m : ℕ} (h : p ^ k ∣ n) (hn : ¬ p ^ (m + 1) ∣ n) :
    k ≤ m := by
  by_contra hk
  exact hn ((Nat.pow_dvd_pow p (by omega)).trans h)

end FinAlt

open FinAlt

theorem noPerfLocal_S7 : NoPerfLocal (Perm (Fin 7)) := by
  have hcard : Nat.card (Perm (Fin 7)) = 5040 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  refine noPerfLocal_of (fun p hp hp2 E hE => rank_of_dvd hp (fun k hk => ?_) E hE)
    (fun p hp hp2 σ hσ => ?_)
  · rw [hcard] at hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · left; omega
    have hpd : p ∣ 5040 := (dvd_pow_self p hk0.ne').trans hk
    have hp7 : p ≤ 7 := by
      by_contra hp7
      push Not at hp7
      have : p ∣ 2 ^ 4 * 3 ^ 2 * 5 * 7 := hpd
      rcases (Nat.Prime.dvd_mul hp).mp this with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
          · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
          · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
        · have := Nat.le_of_dvd (by norm_num) h; omega
      · have := Nat.le_of_dvd (by norm_num) h; omega
    have hp2' := hp.two_le
    have h357 : p = 3 ∨ p = 5 ∨ p = 7 := by
      interval_cases p <;> first | omega | exact absurd hp (by norm_num)
    rcases h357 with rfl | rfl | rfl
    · right
      exact ⟨rfl, le_of_pow_dvd hk (by decide)⟩
    · left
      exact le_of_pow_dvd hk (by decide)
    · left
      exact le_of_pow_dvd hk (by decide)
  · obtain ⟨k, hk1, -, hkp, hc⟩ := card_centralizer_of_prime hp hσ
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hk2 : k ≤ 2 := by nlinarith
    interval_cases k
    ·
      have hp7 : p ≤ 7 := by omega
      have h357 : p = 3 ∨ p = 5 ∨ p = 7 := by
        interval_cases p <;> first | omega | exact absurd hp (by norm_num)
      rcases h357 with rfl | rfl | rfl <;> norm_num at hc
      · exact isSolvable_of_card_eq_pow_mul_pow (a := 3) (b := 2) Nat.prime_two
          Nat.prime_three (by norm_num) (by rw [hc]; decide)
      · exact isSolvable_of_card_eq_pow_mul_pow (a := 1) (b := 1) Nat.prime_two
          (by norm_num : Nat.Prime 5) (by norm_num) (by rw [hc]; decide)
      · exact isSolvable_of_card_eq_pow_mul_pow (a := 0) (b := 1) Nat.prime_two
          (by norm_num : Nat.Prime 7) (by norm_num) (by rw [hc]; decide)
    ·
      have hp3' : p = 3 := by omega
      subst hp3'
      exact isSolvable_of_card_eq_pow_mul_pow (a := 1) (b := 2) Nat.prime_two
        Nat.prime_three (by norm_num) (by rw [hc]; decide)

theorem finCellA_a7 {Y : Type} [Group Y] (h : Nonempty (Y ≃* alternatingGroup (Fin 7))) :
    FinCellA Y := by
  obtain ⟨e⟩ := h
  exact finCellA_of (NoPerfLocal.of_equiv (autTransport (by norm_num) (by norm_num) e)
    noPerfLocal_S7)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
