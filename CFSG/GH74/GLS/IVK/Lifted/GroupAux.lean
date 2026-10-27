module

public import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup

section Zpow

variable {G : Type} [Group G]

theorem exists_mul_zpow_of_mem_sup {O : Subgroup G} {z : G} (hz : z ∈ normalizer (O : Set G)) {g : G}
    (hg : g ∈ O ⊔ zpowers z) : ∃ o ∈ O, ∃ i : ℤ, g = o * z ^ i := by
  have hzi : ∀ (i : ℤ) (n : G), n ∈ O → z ^ i * n * (z ^ i)⁻¹ ∈ O := by
    intro i n hn
    exact (Subgroup.mem_normalizer_iff.1 (Subgroup.zpow_mem _ hz i) n).1 hn
  let H₁ : Subgroup G :=
    { carrier := {g | ∃ o ∈ O, ∃ i : ℤ, g = o * z ^ i}
      one_mem' := ⟨1, O.one_mem, 0, by simp⟩
      mul_mem' := by
        rintro a b ⟨o₁, ho₁, i, rfl⟩ ⟨o₂, ho₂, j, rfl⟩
        refine ⟨o₁ * (z ^ i * o₂ * (z ^ i)⁻¹), O.mul_mem ho₁ (hzi i o₂ ho₂), i + j, ?_⟩
        rw [zpow_add]
        group
      inv_mem' := by
        rintro a ⟨o, ho, i, rfl⟩
        refine ⟨z ^ (-i) * o⁻¹ * (z ^ (-i))⁻¹, hzi (-i) _ (O.inv_mem ho), -i, ?_⟩
        group }
  have hle : O ⊔ zpowers z ≤ H₁ :=
    sup_le (fun o ho => ⟨o, ho, 0, by simp⟩)
      (zpowers_le.2 ⟨1, O.one_mem, 1, by simp⟩)
  exact hle hg

theorem zpow_eq_one_or_self {z : G} (hz2 : z * z = 1) (i : ℤ) : z ^ i = 1 ∨ z ^ i = z := by
  have h2 : z ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    exact hz2
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' i
  · left
    rw [hk, zpow_mul, h2, one_zpow]
  · right
    rw [hk, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem eq_one_of_sq_eq_one_of_odd [Finite G] {O : Subgroup G} (hOodd : Odd (Nat.card ↥O)) {o : G}
    (ho : o ∈ O) (ho2 : o * o = 1) : o = 1 := by
  have h1 : orderOf o ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ho2)
  have h2 : orderOf o ∣ Nat.card ↥O := Subgroup.orderOf_dvd_natCard O ho
  rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
  · exact orderOf_eq_one_iff.1 h
  · exfalso
    rw [h] at h2
    exact (Nat.not_even_iff_odd.2 hOodd) (even_iff_two_dvd.2 h2)

theorem mem_normalizer_of_comm {O : Subgroup G} {z : G} (hzO : ∀ n ∈ O, z * n = n * z) :
    z ∈ normalizer (O : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    have : z * n * z⁻¹ = n := by rw [hzO n hn]; group
    rw [this]
    exact hn
  · intro hm
    have h1 : z * (z * n * z⁻¹) = (z * n * z⁻¹) * z := hzO _ hm
    have h2 : z * n * z⁻¹ = n := by
      calc z * n * z⁻¹ = z⁻¹ * (z * (z * n * z⁻¹)) := by group
        _ = z⁻¹ * ((z * n * z⁻¹) * z) := by rw [h1]
        _ = n := by group
    rw [h2] at hm
    exact hm

theorem eq_one_or_eq_of_mem_sup_zpowers [Finite G] {O : Subgroup G} {z u : G} (hz2 : z * z = 1)
    (hOodd : Odd (Nat.card ↥O)) (hzO : ∀ n ∈ O, z * n = n * z) (hu : u ∈ O ⊔ zpowers z)
    (hu2 : u * u = 1) : u = 1 ∨ u = z := by
  obtain ⟨o, ho, i, rfl⟩ := exists_mul_zpow_of_mem_sup (mem_normalizer_of_comm hzO) hu
  rcases zpow_eq_one_or_self hz2 i with h | h
  · rw [h, mul_one] at hu2 ⊢
    left
    exact eq_one_of_sq_eq_one_of_odd hOodd ho hu2
  · rw [h] at hu2 ⊢
    right
    have hoo : o * o = 1 := by
      have hzo : z * o = o * z := hzO o ho
      calc o * o = o * o * (z * z) := by rw [hz2, mul_one]
        _ = o * (o * z) * z := by group
        _ = o * (z * o) * z := by rw [hzo]
        _ = o * z * (o * z) := by group
        _ = 1 := hu2
    have := eq_one_of_sq_eq_one_of_odd hOodd ho hoo
    rw [this, one_mul]

end Zpow

end CFSG.GH74.GLS.IVK.Lifted
