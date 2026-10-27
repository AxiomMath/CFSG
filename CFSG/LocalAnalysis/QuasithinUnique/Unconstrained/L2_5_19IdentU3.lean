module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentOrd
import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.QuasithinUnique.Ch1
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

section Order

variable {G : Type} [Group G] [Finite G] {X K : Subgroup G} {t : G}

theorem IdentSetting.false_of_dvd_prime
    (hs : IdentSetting X K t) (hK : IsKType K) {N : ℕ}
    (hNpos : 0 < N) (hN : Nat.card (↥X ⧸ Subgroup.center ↥X) ∣ N)
    (h168 : ¬ (168 ∣ N ∧ 168 < N)) (h360 : ¬ (360 ∣ N ∧ 360 < N))
    (hp : ∀ p : ℕ, p.Prime → 17 ≤ p →
      ¬ (p * (p * p - 1) ∣ 2 * N ∧ p * (p * p - 1) < 2 * N)) : False := by
  have hd := (hs.card_dvd hK).trans hN
  have hlt : Nat.card ↥K < N := lt_of_lt_of_le (hs.card_lt hK) (Nat.le_of_dvd hNpos hN)
  rcases isKType_card hK with h | h | ⟨p, hFM, h7, hpk⟩
  · rw [h] at hd hlt
    exact h168 ⟨hd, hlt⟩
  · rw [h] at hd hlt
    exact h360 ⟨hd, hlt⟩
  · refine hp p hFM.1 (seventeen_le_of_isFermatOrMersenne hFM h7) ⟨?_, ?_⟩
    · rw [hpk]
      exact Nat.mul_dvd_mul_left 2 hd
    · rw [hpk]
      omega

end Order

section U3Four

open Ident

variable {G : Type} [Group G] [Finite G]

theorem card_of_statedPSU_three_four {X : Type} [Group X]
    (hm : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 2 2) : Nat.card X = 62400 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_four hm

theorem tabIdentFor_u3Four
    : TabIdentFor @FamU3Four := by
  intro G _ _ X K t hs hX
  exfalso
  have hcard : Nat.card ↥X = 62400 := card_of_statedPSU_three_four hX.2
  have hdvd : Nat.card (↥X ⧸ Subgroup.center ↥X) ∣ 62400 := by
    rw [← hcard]
    exact Subgroup.card_quotient_dvd_card _
  refine hs.false_of_dvd_prime hs.ktype (N := 62400) (by norm_num) hdvd (by norm_num)
    (by norm_num) ?_
  rintro p hpp hp ⟨hd, hlt⟩
  have h1 : p ≤ 49 := by
    by_contra h
    have h50 : 50 ≤ p := by omega
    have : 50 * (50 * 50 - 1) ≤ p * (p * p - 1) :=
      Nat.mul_le_mul h50 (Nat.sub_le_sub_right (Nat.mul_le_mul h50 h50) 1)
    omega
  interval_cases p <;> first | omega | exact absurd hpp (by norm_num)

end U3Four

end CFSG.QuasithinUnique.Id2519
