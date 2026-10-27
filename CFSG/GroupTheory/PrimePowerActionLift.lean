module

public import Mathlib.GroupTheory.Sylow

public noncomputable section

namespace CFSG

universe u v

theorem exists_prime_power_order_representative
    {G : Type u} {A : Type v} [Group G] [Finite G] [Group A]
    (p : ℕ) [Fact p.Prime] (f : G →* A) (a : A) (ha : a ∈ f.range)
    (horder : orderOf a = p) :
    ∃ g : G, f g = a ∧ ∃ k : ℕ, 0 < k ∧ orderOf g = p ^ k := by
  let aR : f.range := ⟨a, ha⟩
  have horderR : orderOf aR = p := by
    rw [← Subgroup.orderOf_coe]
    exact horder
  have hpgroup : IsPGroup p (Subgroup.zpowers aR) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, horderR, pow_one]
  obtain ⟨T, hT⟩ := hpgroup.exists_le_sylow
  obtain ⟨Q, hQ⟩ := Sylow.mapSurjective_surjective f.rangeRestrict_surjective p T
  have haT : aR ∈ (T : Subgroup f.range) := hT (Subgroup.mem_zpowers aR)
  rw [← hQ] at haT
  change aR ∈ (Q : Subgroup G).map f.rangeRestrict at haT
  obtain ⟨g, hg, hga⟩ := Subgroup.mem_map.mp haT
  have hfa : f g = a := congrArg Subtype.val hga
  obtain ⟨k, hk⟩ := Q.isPGroup'.exists_orderOf_eq_pow (⟨g, hg⟩ : Q)
  have hkg : orderOf g = p ^ k := by
    simpa only [← Subgroup.orderOf_coe] using hk
  have hkpos : 0 < k := by
    by_contra h
    have hkzero : k = 0 := by omega
    rw [hkzero, pow_zero, orderOf_eq_one_iff] at hkg
    have hane : a ≠ 1 := by
      intro h
      rw [h, orderOf_one] at horder
      exact (Fact.out : p.Prime).ne_one horder.symm
    exact hane (hfa.symm.trans (hkg ▸ map_one f))
  exact ⟨g, hfa, k, hkpos, hkg⟩

end CFSG
