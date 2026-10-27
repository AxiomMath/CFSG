module

public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.GroupTheory.PCore.CommutingBalance

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

variable {G : Type*} [Group G]

theorem mem_of_coprime_orderOf {p : ℕ} {N : Subgroup G} [N.Normal] (hGN : IsPGroup p (G ⧸ N))
    {g : G} (hg : Nat.Coprime p (orderOf g)) : g ∈ N := by
  obtain ⟨k, hk⟩ := hGN (g : G ⧸ N)
  have h1 : orderOf (g : G ⧸ N) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf (g : G ⧸ N) ∣ orderOf g := orderOf_map_dvd (QuotientGroup.mk' N) g
  have h3 : orderOf (g : G ⧸ N) = 1 := Nat.eq_one_of_dvd_coprimes (hg.pow_left k) h1 h2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem pPrimeCore_map_le_of_isPGroup_quotient [Finite G] {p : ℕ} [Fact p.Prime]
    {N : Subgroup G} [N.Normal] (hGN : IsPGroup p (G ⧸ N)) (H : Subgroup G) :
    (pPrimeCore p H).map H.subtype ≤ N := by
  rintro _ ⟨d, hd, rfl⟩
  refine mem_of_coprime_orderOf hGN ?_
  rw [Subgroup.coe_subtype, Subgroup.orderOf_coe, ← Subgroup.orderOf_mk d hd]
  exact (pPrimeCore_coprime_card (p := p) (G := H)).coprime_dvd_right (orderOf_dvd_natCard _)

theorem normal_prime_power_index_prime_complement_core [Finite G] (p : ℕ) [Fact p.Prime]
    {N : Subgroup G} [hN : N.Normal] (hGN : IsPGroup p (G ⧸ N)) :
    (∀ H : Subgroup G, (pPrimeCore p H).map H.subtype =
        (pPrimeCore p ↥(H ⊓ N)).map (H ⊓ N).subtype) ∧
      ∀ x : G, (pPrimeCore p (centralizer ({x} : Set G))).map
          (centralizer ({x} : Set G)).subtype =
        (pPrimeCore p ↥(N ⊓ centralizer ({x} : Set G))).map
          (N ⊓ centralizer ({x} : Set G)).subtype := by
  have key : ∀ H : Subgroup G, (pPrimeCore p H).map H.subtype =
      (pPrimeCore p ↥(H ⊓ N)).map (H ⊓ N).subtype := by
    intro H
    set M := (H ⊓ N).subgroupOf H with hM
    have hMeq : M = N.subgroupOf H := by
      ext x
      simp [M, Subgroup.mem_subgroupOf]
    have hMn : M.Normal := hMeq ▸ hN.subgroupOf H
    have hint := CFSG.LocalCores.prime_set_core_normal_intersection
      {q : Nat.Primes | q.val ≠ p} hMn
    rw [← CFSG.pPrimeCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore] at hint
    have hDM : pPrimeCore p H ≤ M := by
      intro d hd
      rw [hMeq, Subgroup.mem_subgroupOf]
      exact pPrimeCore_map_le_of_isPGroup_quotient hGN H ⟨d, hd, rfl⟩
    rw [inf_eq_right.2 hDM] at hint
    rw [← hint, ← CFSG.pPrimeCore_map_subgroupOf p (H ⊓ N) H inf_le_left]
  refine ⟨key, fun x => ?_⟩
  rw [key, inf_comm]

end CFSG.LocalAnalysis.ComponentInitial
