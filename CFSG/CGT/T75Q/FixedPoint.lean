module

import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.CGT.T75Q

variable {G : Type*} [Group G]

theorem commutator_injOn {N : Subgroup G} (hN : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) {k : G}
    (hkN : ∀ m ∈ N, k * m * k⁻¹ ∈ N) (hfix : ∀ m ∈ N, k * m * k⁻¹ = m → m = 1) {m m' : G}
    (hm : m ∈ N) (hm' : m' ∈ N) (h : k * m * k⁻¹ * m⁻¹ = k * m' * k⁻¹ * m'⁻¹) : m = m' := by
  have ha : k * m * k⁻¹ ∈ N := hkN m hm
  have ha' : k * m' * k⁻¹ ∈ N := hkN m' hm'
  have h1 : k * m * k⁻¹ = (k * m' * k⁻¹) * (m'⁻¹ * m) := by
    have : k * m * k⁻¹ = (k * m' * k⁻¹ * m'⁻¹) * m := by
      calc k * m * k⁻¹ = (k * m * k⁻¹ * m⁻¹) * m := by group
        _ = (k * m' * k⁻¹ * m'⁻¹) * m := by rw [h]
    rw [this]
    group
  have hd : m * m'⁻¹ ∈ N := N.mul_mem hm (N.inv_mem hm')
  have h2 : k * (m * m'⁻¹) * k⁻¹ = m * m'⁻¹ := by
    have e1 : k * (m * m'⁻¹) * k⁻¹ = (k * m * k⁻¹) * (k * m' * k⁻¹)⁻¹ := by group
    rw [e1, h1]
    have hc1 : (k * m' * k⁻¹) * (m'⁻¹ * m) * (k * m' * k⁻¹)⁻¹ = m'⁻¹ * m := by
      have := hN (k * m' * k⁻¹) ha' (m'⁻¹ * m) (N.mul_mem (N.inv_mem hm') hm)
      calc (k * m' * k⁻¹) * (m'⁻¹ * m) * (k * m' * k⁻¹)⁻¹
          = (m'⁻¹ * m) * (k * m' * k⁻¹) * (k * m' * k⁻¹)⁻¹ := by rw [this]
        _ = m'⁻¹ * m := by group
    rw [hc1]
    exact (Commute.inv_left (show Commute m' m from hN m' hm' m hm)).eq
  have h3 := hfix _ hd h2
  exact mul_inv_eq_one.1 h3

theorem mem_of_commutator_mem {N K : Subgroup G} [Finite K]
    (hN : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hKN : K ≤ N) {k : G}
    (hkN : ∀ m ∈ N, k * m * k⁻¹ ∈ N) (hkK : ∀ m ∈ K, k * m * k⁻¹ ∈ K)
    (hfix : ∀ m ∈ N, k * m * k⁻¹ = m → m = 1) {x : G} (hx : x ∈ N)
    (hxK : k * x * k⁻¹ * x⁻¹ ∈ K) : x ∈ K := by
  let f : K → K := fun m => ⟨k * m * k⁻¹ * (m : G)⁻¹, K.mul_mem (hkK _ m.2) (K.inv_mem m.2)⟩
  have hinj : Function.Injective f := by
    intro m m' h
    have h' : k * (m : G) * k⁻¹ * (m : G)⁻¹ = k * (m' : G) * k⁻¹ * (m' : G)⁻¹ :=
      congrArg Subtype.val h
    exact Subtype.ext (commutator_injOn hN hkN hfix (hKN m.2) (hKN m'.2) h')
  obtain ⟨m, hm⟩ := Finite.injective_iff_surjective.1 hinj ⟨k * x * k⁻¹ * x⁻¹, hxK⟩
  have hm' : k * (m : G) * k⁻¹ * (m : G)⁻¹ = k * x * k⁻¹ * x⁻¹ := congrArg Subtype.val hm
  have := commutator_injOn hN hkN hfix (hKN m.2) hx hm'
  rw [← this]
  exact m.2

end CFSG.CGT.T75Q
