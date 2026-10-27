module

public import CFSG.ClassicalGroups.Unitary.Perfect

public section

namespace CFSG.ClassicalGroups.Unitary

open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

omit [Fact p.Prime] [CharP K p] in
theorem one_lt_pow_of_card (hK : Nat.card K = (p ^ f) ^ 2) : 1 < p ^ f := by
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  rw [hK] at h1
  by_contra h
  have : p ^ f ≤ 1 := not_lt.mp h
  nlinarith [Nat.zero_le (p ^ f)]

omit [Fact p.Prime] [CharP K p] in
theorem card_units_of_card (hK : Nat.card K = (p ^ f) ^ 2) :
    Nat.card Kˣ = (p ^ f) ^ 2 - 1 := by
  classical
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]

theorem sq_sub_one_eq (q : ℕ) (hq : 1 ≤ q) : q ^ 2 - 1 = (q + 1) * (q - 1) := by
  zify [hq, Nat.one_le_pow 2 q (by omega)]
  ring

theorem exists_norm_eq_of_fixed (hK : Nat.card K = (p ^ f) ^ 2) {d : K}
    (hd : unitaryInvolution K p f d = d) (hd0 : d ≠ 0) :
    ∃ c : K, unitaryInvolution K p f c * c = d := by
  have hq := one_lt_pow_of_card hK
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, card_units_of_card hK]
  set D : Kˣ := Units.mk0 d hd0 with hD
  obtain ⟨k, hk⟩ : ∃ k : ℕ, g ^ k = D :=
    (mem_powers_iff_mem_zpowers.mpr (hg D))
  have hDq : D ^ (p ^ f) = D := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hD, Units.val_mk0, ← unitaryInvolution_apply, hd]
  have hDq1 : D ^ (p ^ f - 1) = 1 := by
    have h := hDq
    rw [← Nat.sub_add_cancel hq.le, pow_succ] at h
    exact mul_eq_right.mp h
  have hdvd : (p ^ f) ^ 2 - 1 ∣ k * (p ^ f - 1) := by
    rw [← hord]
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, hk, hDq1]
  rw [sq_sub_one_eq _ hq.le] at hdvd
  obtain ⟨j, rfl⟩ : p ^ f + 1 ∣ k :=
    Nat.dvd_of_mul_dvd_mul_right (by omega) hdvd
  refine ⟨((g ^ j : Kˣ) : K), ?_⟩
  rw [unitaryInvolution_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, ← pow_mul,
    mul_comm j, hk, hD, Units.val_mk0]

theorem exists_norm_ne_one (hK : Nat.card K = (p ^ f) ^ 2) (hq2 : p ^ f ≠ 2) :
    ∃ s : K, s ≠ 0 ∧ unitaryInvolution K p f s * s ≠ 1 := by
  have hq := one_lt_pow_of_card hK
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, card_units_of_card hK]
  refine ⟨(g : K), g.ne_zero, fun h => ?_⟩
  rw [unitaryInvolution_apply, ← pow_succ, ← Units.val_pow_eq_pow_val] at h
  have h1 : g ^ (p ^ f + 1) = 1 := Units.ext (by rw [h, Units.val_one])
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hord, sq_sub_one_eq _ hq.le] at h2
  have h3 := Nat.le_of_dvd (by omega) h2
  have h4 : p ^ f - 1 ≤ 1 := by
    by_contra h5
    push Not at h5
    nlinarith
  omega

theorem isUnitaryInvolution_unitaryInvolution (hK : Nat.card K = (p ^ f) ^ 2) :
    IsUnitaryInvolution (unitaryInvolution K p f) where
  invol := unitaryInvolution_involutive hK
  exists_ne := exists_unitaryInvolution_ne hK
  trace_surj _ ha := exists_add_unitaryInvolution_eq hK ha
  norm_surj _ hd hd0 := exists_norm_eq_of_fixed hK hd hd0

omit [CharP K p] in
theorem charP_of_card_sq (hK : Nat.card K = (p ^ f) ^ 2) : CharP K p := by
  have := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (f := f * 2) (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])

omit [CharP K p] in
theorem isPerfect_statedSU (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (hn : 3 ≤ n)
    (hnq : (n, p ^ f) ≠ (3, 2)) : Group.IsPerfect (StatedSU n (p ^ f) K) := by
  have := charP_of_card_sq (p := p) (f := f) hK
  rw [← SUid_eq_statedSU hK n]
  exact isPerfect_SUid (isUnitaryInvolution_unitaryInvolution hK) hn fun h3 =>
    exists_norm_ne_one hK fun hq => hnq (by rw [h3, hq])

end CFSG.ClassicalGroups.Unitary
