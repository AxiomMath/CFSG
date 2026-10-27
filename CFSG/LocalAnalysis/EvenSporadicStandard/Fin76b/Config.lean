module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem mem_zpowers_sq_eq_one {G : Type*} [Group G] {z : G} (hz : z * z = 1) {c : G}
    (hc : c ∈ zpowers z) : c = 1 ∨ c = z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    obtain ⟨m, hm⟩ : ∃ m, k = 2 * m := ⟨k / 2, by omega⟩
    rw [hm, zpow_mul, h2, one_zpow]
  · right
    obtain ⟨m, hm⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
    rw [hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

structure InnerConfig (G : Type*) [Group G] (A : Subgroup G) (z t : G) (T₀ : Subgroup G) :
    Prop where
  z_sq : z * z = 1
  z_ne : z ≠ 1
  z_cent : z ∈ centralizer (A : Set G)
  disjoint : Disjoint A (zpowers z)
  cent_eq : centralizer ({z} : Set G) = A ⊔ zpowers z
  T₀_le : T₀ ≤ A
  T₀_pgroup : IsPGroup 2 T₀
  T₀_odd : ∃ m, Odd m ∧ Nat.card A = Nat.card T₀ * m
  t_sq : t * t = 1
  t_ne : t ≠ 1
  t_mem : t ∈ T₀
  t_central : ∀ x ∈ T₀, x * t = t * x
  center_le : ∀ y ∈ T₀, (∀ x ∈ T₀, x * y = y * x) → y = 1 ∨ y = t
  t_square : ∃ g ∈ A, g * g = t
  classes : ∃ b ∈ A, ∀ a ∈ A, a * a = 1 → a ≠ 1 →
    (∃ c ∈ A, a = c * t * c⁻¹) ∨ (∃ c ∈ A, a = c * b * c⁻¹)

namespace InnerConfig

variable {G : Type*} [Group G] {A : Subgroup G} {z t : G} {T₀ : Subgroup G}
  (h : InnerConfig G A z t T₀)

include h in
theorem z_not_mem_A : z ∉ A := fun hz => h.z_ne (by
  have : z ∈ A ⊓ zpowers z := ⟨hz, mem_zpowers z⟩
  rw [h.disjoint.eq_bot, mem_bot] at this
  exact this)

include h in
theorem zpowers_le_centralizer : zpowers z ≤ centralizer (T₀ : Set G) := by
  rw [zpowers_le]
  exact mem_centralizer_iff.2 fun y hy => mem_centralizer_iff.1 h.z_cent y (h.T₀_le hy)

include h in
theorem t_mem_A : t ∈ A := h.T₀_le h.t_mem

include h in
theorem z_comm_of_mem_A {a : G} (ha : a ∈ A) : a * z = z * a :=
  mem_centralizer_iff.1 h.z_cent a ha

include h in
theorem T₀_disjoint : Disjoint T₀ (zpowers z) :=
  h.disjoint.mono_left h.T₀_le

include h in
theorem mem_T_iff {x : G} : x ∈ T₀ ⊔ zpowers z ↔ ∃ s ∈ T₀, x = s ∨ x = s * z := by
  constructor
  · intro hx
    obtain ⟨s, hs, c, hc, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_centralizer h.zpowers_le_centralizer hx
    rcases mem_zpowers_sq_eq_one h.z_sq hc with rfl | rfl
    · exact ⟨s, hs, Or.inl (mul_one s)⟩
    · exact ⟨s, hs, Or.inr rfl⟩
  · rintro ⟨s, hs, rfl | rfl⟩
    · exact mem_sup_left hs
    · exact mul_mem (mem_sup_left hs) (mem_sup_right (mem_zpowers z))

theorem z_mem_T (T₀ : Subgroup G) (z : G) : z ∈ T₀ ⊔ zpowers z := mem_sup_right (mem_zpowers z)

include h in
theorem t_mem_T : t ∈ T₀ ⊔ zpowers z := mem_sup_left h.t_mem

theorem T₀_le_T (T₀ : Subgroup G) (z : G) : T₀ ≤ T₀ ⊔ zpowers z := le_sup_left

include h in
theorem z_not_mem_T₀ : z ∉ T₀ := fun hz => h.z_not_mem_A (h.T₀_le hz)

include h in
theorem z_order : orderOf z = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact h.z_sq) h.z_ne

include h in
theorem t_order : orderOf t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact h.t_sq) h.t_ne

include h in
theorem T_card [Finite G] : Nat.card (T₀ ⊔ zpowers z : Subgroup G) = 2 * Nat.card T₀ := by
  have e := mulEquivProdSup h.zpowers_le_centralizer h.T₀_disjoint
  rw [Nat.card_congr e.toEquiv.symm, Nat.card_prod, Nat.card_zpowers, h.z_order]
  ring

end InnerConfig

end CFSG.EvenSporadicStandard.Fin76b
