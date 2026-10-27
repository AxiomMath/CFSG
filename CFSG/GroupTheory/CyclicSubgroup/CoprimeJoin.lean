module


public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.GroupTheory.CyclicSubgroup

theorem isCyclic_sup_of_coprime {G : Type*} [Group G] [Finite G] (A D : Subgroup G)
    (hA : IsCyclic A) (hD : IsCyclic D) (hc : ∀ a ∈ A, ∀ d ∈ D, Commute a d)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card D)) : IsCyclic (A ⊔ D : Subgroup G) := by
  have mem_zpowers_mul (a d : G) (hcomm : Commute a d)
      (hcop : Nat.Coprime (orderOf a) (orderOf d)) : a ∈ Subgroup.zpowers (a * d) := by
    obtain ⟨k, hk1, hk0⟩ := Nat.chineseRemainder hcop 1 0
    have h1 : a ^ k = a ^ (1 : ℕ) := by
      rw [← pow_mod_orderOf, show k % orderOf a = 1 % orderOf a from hk1, pow_mod_orderOf]
    have h2 : d ^ k = 1 := by
      rw [← pow_mod_orderOf, show k % orderOf d = 0 % orderOf d from hk0]
      simp
    have : (a * d) ^ k = a := by
      rw [hcomm.mul_pow, h1, h2]
      simp
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using this⟩
  obtain ⟨a, ha⟩ := hA.exists_generator
  obtain ⟨d, hd⟩ := hD.exists_generator
  have hoa : orderOf (a : G) = Nat.card A := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers ha]
  have hod : orderOf (d : G) = Nat.card D := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hd]
  have hcomm : Commute (a : G) (d : G) := hc a a.2 d d.2
  have hcop' : Nat.Coprime (orderOf (a : G)) (orderOf (d : G)) := by
    simpa [hoa, hod] using hcop
  have h1 : (a : G) ∈ Subgroup.zpowers ((a : G) * d) :=
    mem_zpowers_mul (a : G) (d : G) hcomm hcop'
  have h2 : (d : G) ∈ Subgroup.zpowers ((a : G) * d) := by
    have := mem_zpowers_mul (d : G) (a : G) hcomm.symm hcop'.symm
    rwa [← hcomm.eq] at this
  have hAle : A ≤ Subgroup.zpowers ((a : G) * d) := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (ha ⟨x, hx⟩)
    have : x = (a : G) ^ k := by simpa using (congrArg Subtype.val hk).symm
    rw [this]
    exact Subgroup.zpow_mem _ h1 k
  have hDle : D ≤ Subgroup.zpowers ((a : G) * d) := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hd ⟨x, hx⟩)
    have : x = (d : G) ^ k := by simpa using (congrArg Subtype.val hk).symm
    rw [this]
    exact Subgroup.zpow_mem _ h2 k
  have hle : A ⊔ D ≤ Subgroup.zpowers ((a : G) * d) := sup_le hAle hDle
  have hge : Subgroup.zpowers ((a : G) * d) ≤ A ⊔ D := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left a.2) (Subgroup.mem_sup_right d.2)
  have : A ⊔ D = Subgroup.zpowers ((a : G) * d) := le_antisymm hle hge
  rw [this]
  infer_instance

end CFSG.GroupTheory.CyclicSubgroup
