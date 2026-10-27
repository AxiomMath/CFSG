module

public import CFSG.CGT.Timmesfeld75.Sec3TenCaseB5
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.Timmesfeld75.Sec6Four

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem Sec6Ctx.card_centralizer_sq (hc : Sec6Ctx T T₁ n m) {x : G} (hx : x ∈ normD T) :
    Nat.card T ≤ Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) ^ 2 := by
  have := hc.finite
  have hT := hc.hy.pair.wc.1
  exact card_le_sq_centralizer hT (mul_self_eq_one_of_mem_classD hT hx.1)
    fun v hv => conj_mem_of_mem_normalizer hx.2 hv

theorem Sec6Ctx.big_of_card_lt (hc : Sec6Ctx T T₁ n m) {x : G} (hx : x ∈ normD T)
    (hlt : Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) < Nat.card ↥(normIn T T₁))
    (hne : ¬ (Nat.card T = 16 ∧ Nat.card ↥(normIn T T₁) = 8 ∧
      Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) = 4)) : 32 ≤ Nat.card T := by
  have := hc.finite
  by_contra hsmall
  rw [not_le] at hsmall
  have hTn : Nat.card T = 2 ^ (m * n) := by rw [hc.hT, pow_mul]
  have hLn : Nat.card ↥(normIn T T₁) = 2 ^ (m * (n - 1)) := by rw [hc.card_normIn, pow_mul]
  have h4 : 4 ≤ Nat.card T := hc.hy.card
  have hsq := hc.card_centralizer_sq hx
  have hCdvd : Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) ∣ Nat.card T :=
    Subgroup.card_dvd_of_le inf_le_left
  have hL2 : 1 < Nat.card ↥(normIn T T₁) := (Subgroup.one_lt_card_iff_ne_bot _).2 hc.sec3.cfg.ne
  have hCpos : 0 < Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) := Nat.card_pos
  generalize Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) = c at hlt hne hsq hCdvd hCpos
  rw [hLn] at hlt hne hL2
  rw [hTn] at hsmall hsq hCdvd hne h4
  have hmn5 : m * n < 5 := by
    by_contra h
    rw [not_lt] at h
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h
    omega
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      rw [zero_mul, pow_zero] at hL2
      omega
    · exact h
  have hn2 : 2 ≤ n := by
    by_contra h
    have hn1 : n - 1 = 0 := by omega
    rw [hn1, mul_zero, pow_zero] at hL2
    omega
  have hn4 : n ≤ 4 := by nlinarith
  have hm4 : m ≤ 2 := by nlinarith
  interval_cases m <;> interval_cases n <;>
    simp only [Nat.reduceMul, Nat.reduceSub, Nat.reducePow] at hlt hne hsq hCdvd hsmall h4 hmn5 <;>
    first | omega | (interval_cases c <;> simp_all)

end CFSG.CGT.Timmesfeld75
