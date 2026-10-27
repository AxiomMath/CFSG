module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Basic

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type*} [Group G]

private lemma zpow_eq_one_or_self_of_sq_eq_one {y : G} (h : y ^ 2 = 1) (i : ℤ) :
    y ^ i = 1 ∨ y ^ i = y := by
  have hmod : y ^ i = y ^ (i % 2) := zpow_eq_zpow_emod' i h
  have hnn : 0 ≤ i % 2 := Int.emod_nonneg i (by norm_num)
  have hlt : i % 2 < 2 := Int.emod_lt_of_pos i (by norm_num)
  rcases (by omega : i % 2 = 0 ∨ i % 2 = 1) with h0 | h1
  · left; rw [hmod, h0]; simp
  · right; rw [hmod, h1]; simp

private lemma zpow_sq (x : G) (i : ℤ) : (x ^ i) ^ 2 = (x ^ 2) ^ i := by
  rw [← zpow_natCast, ← zpow_mul, zpow_mul', zpow_natCast]

theorem orderOf_eq_four_of_pow {x : G} (h4 : x ^ 4 = 1) (h2 : x ^ 2 ≠ 1) : orderOf x = 4 :=
  orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using h2) (by simpa using h4)

theorem WreathRel.of_pow {x₁ x₂ lam : G} (h1 : x₁ ^ 4 = 1) (h1' : x₁ ^ 2 ≠ 1) (h2 : x₂ ^ 4 = 1)
    (h2' : x₂ ^ 2 ≠ 1) (hc : x₁ * x₂ = x₂ * x₁) (hne : x₁ ^ 2 ≠ x₂ ^ 2) (hl : lam ^ 2 = 1)
    (hl' : lam ≠ 1) (hconj : lam * x₁ * lam⁻¹ = x₂) : WreathRel x₁ x₂ lam := by
  have hord1 : orderOf x₁ = 4 := orderOf_eq_four_of_pow h1 h1'
  have hord2 : orderOf x₂ = 4 := orderOf_eq_four_of_pow h2 h2'
  refine ⟨hord1, hord2, hc, ?_, orderOf_eq_prime hl hl', hconj⟩
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hg.1
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hg.2
  have heq : x₁ ^ i = x₂ ^ j := hi.trans hj.symm
  have h1sq : (x₁ ^ 2) ^ 2 = 1 := by
    have h : (x₁ ^ 2) ^ 2 = x₁ ^ 4 := by rw [← pow_mul]
    rw [h, h1]
  have h2sq : (x₂ ^ 2) ^ 2 = 1 := by
    have h : (x₂ ^ 2) ^ 2 = x₂ ^ 4 := by rw [← pow_mul]
    rw [h, h2]
  have hsq : (x₁ ^ 2) ^ i = (x₂ ^ 2) ^ j := by
    rw [← zpow_sq x₁ i, ← zpow_sq x₂ j, heq]
  have hA := zpow_eq_one_or_self_of_sq_eq_one h1sq i
  have hB := zpow_eq_one_or_self_of_sq_eq_one h2sq j
  have hA1 : (x₁ ^ 2) ^ i = 1 := by
    rcases hA with hA | hA
    · exact hA
    · rcases hB with hB' | hB'
      · exact absurd ((hA ▸ hsq).trans hB') h1'
      · exact absurd ((hA ▸ hsq).trans hB') hne
  have hord_sq1 : orderOf (x₁ ^ 2) = 2 := by
    refine orderOf_eq_prime ?_ h1'
    calc (x₁ ^ 2) ^ 2 = x₁ ^ (2 * 2) := by rw [← pow_mul]
      _ = x₁ ^ 4 := by norm_num
      _ = 1 := h1
  have hdvd : (2 : ℤ) ∣ i := by
    simpa [hord_sq1] using
      (orderOf_dvd_iff_zpow_eq_one (x := x₁ ^ 2) (i := i)).mpr hA1
  obtain ⟨k, hk⟩ := hdvd
  have hi2 : x₁ ^ i = (x₁ ^ 2) ^ k := by
    rw [hk]
    calc x₁ ^ (2 * k) = (x₁ ^ (2 : ℤ)) ^ k := zpow_mul x₁ 2 k
      _ = (x₁ ^ 2) ^ k := congrArg (fun y => y ^ k) (zpow_natCast x₁ 2)
  have hcase1 : x₁ ^ i = 1 ∨ x₁ ^ i = x₁ ^ 2 := by
    rcases zpow_eq_one_or_self_of_sq_eq_one h1sq k with h | h
    · exact Or.inl (by rw [hi2, h])
    · exact Or.inr (by rw [hi2, h])
  have hB1 : (x₂ ^ 2) ^ j = 1 := by
    rcases hB with hB | hB
    · exact hB
    · exact absurd ((hA1 ▸ hsq).trans hB).symm h2'
  have hord_sq2 : orderOf (x₂ ^ 2) = 2 := by
    refine orderOf_eq_prime ?_ h2'
    calc (x₂ ^ 2) ^ 2 = x₂ ^ (2 * 2) := by rw [← pow_mul]
      _ = x₂ ^ 4 := by norm_num
      _ = 1 := h2
  have hdvd2 : (2 : ℤ) ∣ j := by
    simpa [hord_sq2] using
      (orderOf_dvd_iff_zpow_eq_one (x := x₂ ^ 2) (i := j)).mpr hB1
  obtain ⟨m, hm⟩ := hdvd2
  have hj2 : x₂ ^ j = (x₂ ^ 2) ^ m := by
    rw [hm]
    calc x₂ ^ (2 * m) = (x₂ ^ (2 : ℤ)) ^ m := zpow_mul x₂ 2 m
      _ = (x₂ ^ 2) ^ m := congrArg (fun y => y ^ m) (zpow_natCast x₂ 2)
  have hcase2 : x₂ ^ j = 1 ∨ x₂ ^ j = x₂ ^ 2 := by
    rcases zpow_eq_one_or_self_of_sq_eq_one h2sq m with h | h
    · exact Or.inl (by rw [hj2, h])
    · exact Or.inr (by rw [hj2, h])
  rw [← hi]
  rcases hcase1 with h1c | h1c
  · exact h1c
  · rcases hcase2 with h2c | h2c
    · exact absurd ((h1c ▸ heq).trans h2c) h1'
    · exact absurd ((h1c ▸ heq).trans h2c) hne

theorem M12Rel.of_pow {x₁ x₂ lam tau : G} (h : WreathRel x₁ x₂ lam) (ht : tau ^ 2 = 1)
    (ht' : tau ≠ 1) (hlt : lam * tau = tau * lam) (h1 : tau * x₁ * tau⁻¹ = x₁⁻¹)
    (h2 : tau * x₂ * tau⁻¹ = x₂⁻¹) : M12Rel x₁ x₂ lam tau :=
  { toWreathRel := h
    ord_tau := orderOf_eq_prime ht ht'
    comm_lam_tau := hlt
    tau_x₁ := h1
    tau_x₂ := h2 }

end CFSG.OddStandard.SmallF3.HarrisU33
