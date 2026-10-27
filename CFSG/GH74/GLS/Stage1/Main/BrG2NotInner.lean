module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

open Subgroup CFSG CFSG.ABGLocalTools

namespace CFSG.GH74.GLS.Stage1.Main

theorem mem_of_pow_normalizes_sylow {Y : Type} [Group Y] [Finite Y] {K P : Subgroup Y}
    (hPs : IsSylowOf 2 P K) {k : Y} (hkK : k ∈ K) (hk2 : ∃ m : ℕ, k ^ (2 ^ m) = 1)
    (hkP : k ∈ normalizer (P : Set Y)) : k ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzp : IsPGroup 2 ↥(zpowers k) := by
    obtain ⟨m, hm⟩ := hk2
    have hdvd : orderOf k ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    apply IsPGroup.of_card (n := j)
    rw [Nat.card_zpowers, hj]
  have hsup : IsPGroup 2 ↥(P ⊔ zpowers k) :=
    hPs.isPGroup.to_sup_of_normal_left' hzp (Subgroup.zpowers_le.2 hkP)
  have hQK : P ⊔ zpowers k ≤ K := sup_le hPs.le (Subgroup.zpowers_le.2 hkK)
  have heq := hPs.eq_of_le (le_sup_left : P ≤ P ⊔ zpowers k) hQK hsup
  rw [← heq]
  exact Subgroup.mem_sup_right (mem_zpowers k)

theorem not_inner_of_no_centralizer {Y : Type} [Group Y] [Finite Y] {K P : Subgroup Y}
    (hPs : IsSylowOf 2 P K) {u : Y} (hu2 : u * u = 1) (huP : u ∈ normalizer (P : Set Y))
    (hZ : ∀ c ∈ K, (∀ x ∈ K, c * x = x * c) → c * c = 1)
    (hout : ∀ p ∈ P, ∃ x ∈ K, (u * p⁻¹) * x ≠ x * (u * p⁻¹)) :
    ∀ k ∈ K, ∃ x ∈ K, u * x * u⁻¹ ≠ k * x * k⁻¹ := by
  intro k hkK
  by_contra hcon
  push Not at hcon
  have hPK : P ≤ K := hPs.le
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hk2 : ∀ x ∈ K, k * k * x = x * (k * k) := by
    intro x hx
    have h1 := hcon (k * x * k⁻¹) (K.mul_mem (K.mul_mem hkK hx) (K.inv_mem hkK))
    have h2 : u * (k * x * k⁻¹) * u⁻¹ = x := by
      rw [← hcon x hx, hui]
      calc u * (u * x * u) * u = (u * u) * x * (u * u) := by group
        _ = x := by rw [hu2]; group
    rw [h2] at h1
    calc k * k * x = (k * (k * x * k⁻¹) * k⁻¹) * (k * k) := by group
      _ = x * (k * k) := by rw [← h1]
  have hkk : k * k * (k * k) = 1 := hZ (k * k) (K.mul_mem hkK hkK) hk2
  have hk4 : k ^ (2 ^ 2) = 1 := by
    calc k ^ (2 ^ 2) = k * k * (k * k) := by
          rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
          simp [pow_succ, mul_assoc]
      _ = 1 := hkk
  have hkN : k ∈ normalizer (P : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [← hcon h (hPK hh)]
      exact (Subgroup.mem_normalizer_iff.1 huP h).1 hh
    · intro hh
      have hhK : h ∈ K := by
        have h0 : k⁻¹ * (k * h * k⁻¹) * k ∈ K :=
          K.mul_mem (K.mul_mem (K.inv_mem hkK) (hPK hh)) hkK
        have e : k⁻¹ * (k * h * k⁻¹) * k = h := by group
        rwa [e] at h0
      rw [← hcon h hhK] at hh
      exact (Subgroup.mem_normalizer_iff.1 huP h).2 hh
  have hkP : k ∈ P := mem_of_pow_normalizes_sylow hPs hkK ⟨2, hk4⟩ hkN
  have hcent : ∀ x ∈ K, (u * k⁻¹) * x = x * (u * k⁻¹) := by
    intro x hx
    have hy : k⁻¹ * x * k ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hkK) hx) hkK
    have h1 := hcon (k⁻¹ * x * k) hy
    have h2 : k * (k⁻¹ * x * k) * k⁻¹ = x := by group
    rw [h2, hui] at h1
    calc (u * k⁻¹) * x = u * (k⁻¹ * x * k) * k⁻¹ := by group
      _ = u * (k⁻¹ * x * k) * (u * u) * k⁻¹ := by rw [hu2, mul_one]
      _ = (u * (k⁻¹ * x * k) * u) * (u * k⁻¹) := by group
      _ = x * (u * k⁻¹) := by rw [h1]
  obtain ⟨x, hxK, hx⟩ := hout k hkP
  exact hx (hcent x hxK)

end CFSG.GH74.GLS.Stage1.Main
