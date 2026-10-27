module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GH74.AS16

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem card_lt_of_le_of_not_mem [Finite G] {H K : Subgroup G} (hHK : H ≤ K) {x : G} (hxK : x ∈ K)
    (hxH : x ∉ H) : Nat.card H < Nat.card K := by
  by_contra hge
  push Not at hge
  exact hxH ((Subgroup.eq_of_le_of_card_ge hHK hge) ▸ hxK)

theorem le_normalizer_of_forall_comm {K U : Subgroup G} (hc : ∀ k ∈ K, ∀ u ∈ U, k * u = u * k) :
    K ≤ normalizer (U : Set G) := by
  intro k hk
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h' : k * y * k⁻¹ = y := by rw [hc k hk y hy]; group
    rw [h']
    exact hy
  · intro hy
    have h1 := hc k⁻¹ (K.inv_mem hk) _ hy
    have h2 : y = k * y * k⁻¹ := by
      calc y = k⁻¹ * (k * y * k⁻¹) * k := by group
        _ = ((k * y * k⁻¹) * k⁻¹) * k := by rw [h1]
        _ = k * y * k⁻¹ := by group
    rw [h2]
    exact hy

theorem le_normalizer_of_conj_mem {K Y : Subgroup G} (hK : ∀ x ∈ K, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y) :
    K ≤ normalizer (Y : Set G) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro y
  constructor
  · exact hK x hx y
  · intro hy
    have := hK x⁻¹ (K.inv_mem hx) _ hy
    simpa [mul_assoc] using this

end CFSG.GH74.AS16
