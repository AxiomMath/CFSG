module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open Subgroup

theorem exists_normal_twoComplement {G : Type*} [Group G] [Finite G] (H A : Subgroup G)
    (hAH : A ≤ H) (hAcen : ∀ a ∈ A, ∀ h ∈ H, a * h = h * a)
    (hA : Nat.card A = 2 ^ (Nat.card H).factorization 2) :
    ∃ K : Subgroup G, K ≤ H ∧ (∀ h ∈ H, (h ∈ K ↔ Odd (orderOf h))) ∧
      Nat.card H = Nat.card A * Nat.card K ∧ (∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) := by
  have hcardA : Nat.card (A.subgroupOf H) = 2 ^ (Nat.card H).factorization 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv).trans hA
  obtain ⟨P, hPA⟩ : ∃ P : Sylow 2 H, (P : Subgroup H) = A.subgroupOf H :=
    ⟨Sylow.ofCard (A.subgroupOf H) hcardA, Sylow.coe_ofCard _ _⟩
  have hP : normalizer (P : Subgroup H) ≤ centralizer (P : Set H) := by
    intro n _
    rw [mem_centralizer_iff]
    intro x hx
    have hxP : x ∈ (P : Subgroup H) := hx
    rw [hPA] at hxP
    exact Subtype.ext (hAcen x hxP n n.2)
  haveI : Finite (Sylow 2 H) := Sylow.finite_of_finiteIndex P
  have hcompl := MonoidHom.ker_transferSylow_isComplement' P hP
  have hodd := MonoidHom.not_dvd_card_ker_transferSylow P hP
  generalize MonoidHom.transferSylow P hP = φ at hcompl hodd
  refine ⟨φ.ker.map H.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · intro h hh
    constructor
    · intro hmem
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hmem
      have hcard : Odd (Nat.card φ.ker) := Nat.odd_iff.2 (by omega)
      rw [orderOf_injective H.subtype H.subtype_injective k]
      exact hcard.of_dvd_nat (Subgroup.orderOf_dvd_natCard φ.ker hk)
    · intro hord
      refine Subgroup.mem_map.2 ⟨⟨h, hh⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker]
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := 2)).1 P.isPGroup' (φ ⟨h, hh⟩)
      have hdvd : orderOf (φ ⟨h, hh⟩) ∣ orderOf (⟨h, hh⟩ : H) := orderOf_map_dvd φ _
      rw [hk, Subgroup.orderOf_mk] at hdvd
      have hk0 : k = 0 := by
        by_contra hne
        obtain ⟨m, hm⟩ := hord
        obtain ⟨c, hc⟩ := (dvd_pow_self 2 hne).trans hdvd
        omega
      rw [hk0, pow_zero] at hk
      exact orderOf_eq_one_iff.1 hk
  · have h1 := hcompl.card_mul_card
    have h2 : Nat.card (P : Subgroup H) = Nat.card A := by
      rw [hPA]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv
    rw [Subgroup.card_subtype, ← h2, mul_comm]
    exact h1.symm
  · intro h hh k hk
    obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.1 hk
    have hconj : (⟨h, hh⟩ : H) * k' * (⟨h, hh⟩ : H)⁻¹ ∈ φ.ker :=
      (MonoidHom.normal_ker φ).conj_mem k' hk' ⟨h, hh⟩
    exact Subgroup.mem_map.2 ⟨_, hconj, rfl⟩

end CFSG.EvenSporadicStandard.M12Std.Yosh
