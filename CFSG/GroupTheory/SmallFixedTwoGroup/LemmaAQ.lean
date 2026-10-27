module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

open Subgroup

private theorem zpow_eq_one_or_self {T : Type*} [Group T] {z : T} (hz2 : z * z = 1) (k : ℤ) :
    z ^ k = 1 ∨ z ^ k = z := by
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hz2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hz2, one_zpow, one_mul, zpow_one]

theorem exists_index_two_involutions_central_of_order_four_quotient
    {T : Type*} [Group T] [Finite T] (hcard : Nat.card T = 16) {z : T} (hz : z ∈ center T)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) {p : T} (hp1 : p * p ≠ 1) (hp2 : p * p ≠ z)
    (hp4 : p ^ 4 = 1 ∨ p ^ 4 = z) :
    ∃ M : Subgroup T, M.index = 2 ∧ ∀ u ∈ M, u * u = 1 → u ∈ center T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzle : zpowers z ≤ center T := Subgroup.zpowers_le.2 hz
  haveI hN : (zpowers z).Normal := Subgroup.normal_of_le_center hzle
  have hzp : ∀ w ∈ zpowers z, w = 1 ∨ w = z := by
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    exact zpow_eq_one_or_self hz2 k
  have hordz : orderOf z = 2 := orderOf_eq_prime (by rwa [pow_two]) hz1
  have hNcard : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, hordz]
  have hQcard : Nat.card (T ⧸ zpowers z) = 8 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (zpowers z)
    rw [hNcard, hcard] at h
    omega
  let π : T →* T ⧸ zpowers z := QuotientGroup.mk' (zpowers z)
  have hπker : ∀ g, π g = 1 ↔ g ∈ zpowers z := fun g => QuotientGroup.eq_one_iff g
  have hπp4 : (π p) ^ 2 ^ (1 + 1) = 1 := by
    rw [← map_pow, hπker]
    rcases hp4 with h | h
    · rw [show p ^ 2 ^ (1 + 1) = p ^ 4 from rfl, h]; exact one_mem _
    · rw [show p ^ 2 ^ (1 + 1) = p ^ 4 from rfl, h]; exact mem_zpowers z
  have hπp2 : ¬ (π p) ^ 2 ^ 1 = 1 := by
    rw [← map_pow, hπker]
    intro h
    rcases hzp _ h with h1 | h1
    · exact hp1 (by rw [← pow_two]; exact h1)
    · exact hp2 (by rw [← pow_two]; exact h1)
  have hordπ : orderOf (π p) = 2 ^ (1 + 1) := orderOf_eq_prime_pow hπp2 hπp4
  have hcardP : Nat.card (zpowers (π p)) = 4 := by
    rw [Nat.card_zpowers, hordπ]; rfl
  let M : Subgroup T := (zpowers (π p)).comap π
  have hidx : M.index = 2 := by
    have h1 : M.index = (zpowers (π p)).index :=
      Subgroup.index_comap_of_surjective (zpowers (π p)) (f := π) (QuotientGroup.mk'_surjective _)
    have h2 := Subgroup.card_mul_index (zpowers (π p))
    rw [hcardP, hQcard] at h2
    rw [h1]; omega
  have hmem : ∀ u ∈ M, ∃ (k : ℤ) (w : T), w ∈ zpowers z ∧ u = p ^ k * w := by
    intro u hu
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_comap.1 hu)
    refine ⟨k, (p ^ k)⁻¹ * u, ?_, by group⟩
    rw [← QuotientGroup.eq]
    change π (p ^ k) = π u
    rw [map_zpow]; exact hk
  have hsq : ∀ (k : ℤ) (w : T), w ∈ center T → w * w = 1 →
      (p ^ k * w) * (p ^ k * w) = p ^ (k + k) := by
    intro k w hw hww
    have hc : p ^ k * w = w * p ^ k := Subgroup.mem_center_iff.1 hw (p ^ k)
    calc (p ^ k * w) * (p ^ k * w) = p ^ k * (w * p ^ k) * w := by group
      _ = p ^ k * (p ^ k * w) * w := by rw [← hc]
      _ = p ^ k * p ^ k * (w * w) := by group
      _ = p ^ (k + k) := by rw [hww, mul_one, zpow_add]
  refine ⟨M, hidx, ?_⟩
  intro u hu hu2
  obtain ⟨k, w, hw, rfl⟩ := hmem u hu
  have hwc : w ∈ center T := hzle hw
  have hww : w * w = 1 := by
    rcases hzp w hw with h | h
    · rw [h, mul_one]
    · rw [h]; exact hz2
  have hpk : p ^ (k + k) = 1 := by rw [← hsq k w hwc hww]; exact hu2
  rcases hp4 with h4 | h4
  ·
    have hordp : orderOf p = 2 ^ (1 + 1) := by
      refine orderOf_eq_prime_pow ?_ ?_
      · rw [pow_one, pow_two]; exact hp1
      · exact h4
    have hdvd : ((orderOf p : ℕ) : ℤ) ∣ k + k := orderOf_dvd_iff_zpow_eq_one.2 hpk
    rw [hordp] at hdvd
    obtain ⟨m, hm⟩ := hdvd
    have hk2 : k = 2 * m := by push_cast at hm; omega
    haveI hMn : M.Normal := Subgroup.normal_of_index_eq_two hidx
    have hpM : p ∈ M := Subgroup.mem_comap.2 (by
      change π p ∈ zpowers (π p)
      exact mem_zpowers _)
    have hq2 : (p * p) * (p * p) = 1 := by
      calc (p * p) * (p * p) = p ^ 4 := by
            rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
        _ = 1 := h4
    have hq : p * p ∈ center T := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hgp : g * p * g⁻¹ ∈ M := hMn.conj_mem p hpM g
      obtain ⟨j, w', hw', hj⟩ := hmem _ hgp
      have hw'c : w' ∈ center T := hzle hw'
      have hw'w : w' * w' = 1 := by
        rcases hzp w' hw' with h | h
        · rw [h, mul_one]
        · rw [h]; exact hz2
      have hconj : g * (p * p) * g⁻¹ = p ^ (j + j) := by
        calc g * (p * p) * g⁻¹ = (g * p * g⁻¹) * (g * p * g⁻¹) := by group
          _ = (p ^ j * w') * (p ^ j * w') := by rw [← hj]
          _ = p ^ (j + j) := hsq j w' hw'c hw'w
      have hjj : p ^ (j + j) = (p * p) ^ j := by
        rw [← two_mul, zpow_mul, zpow_two]
      rw [hjj] at hconj
      rcases zpow_eq_one_or_self hq2 j with h | h
      · exfalso
        rw [h] at hconj
        apply hp1
        calc p * p = g⁻¹ * (g * (p * p) * g⁻¹) * g := by group
          _ = 1 := by rw [hconj]; group
      · rw [h] at hconj
        calc g * (p * p) = g * (p * p) * g⁻¹ * g := by group
          _ = (p * p) * g := by rw [hconj]
    have hpk' : p ^ k = (p * p) ^ m := by rw [hk2, zpow_mul, zpow_two]
    rw [hpk']
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hq m) hwc
  ·
    have hordp : orderOf p = 2 ^ (2 + 1) := by
      refine orderOf_eq_prime_pow ?_ ?_
      · intro h
        have h' : p ^ 4 = 1 := h
        rw [h4] at h'
        exact hz1 h'
      · have h8 : p ^ 2 ^ (2 + 1) = p ^ 4 * p ^ 4 := by rw [← pow_add]; norm_num
        rw [h8, h4]
        exact hz2
    have hdvd : ((orderOf p : ℕ) : ℤ) ∣ k + k := orderOf_dvd_iff_zpow_eq_one.2 hpk
    rw [hordp] at hdvd
    obtain ⟨m, hm⟩ := hdvd
    have hk4 : k = 4 * m := by push_cast at hm; omega
    have hpk' : p ^ k = z ^ m := by rw [hk4, zpow_mul, ← h4]; norm_cast
    rw [hpk']
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hz m) hwc

end CFSG.GroupTheory.SmallFixedTwoGroup
