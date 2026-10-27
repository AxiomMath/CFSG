module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Order.BourbakiWitt
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

private theorem sup_closure_insert {G : Type*} [Group G] (K : Subgroup G) (a : G) (t : Set G) :
    K ⊔ Subgroup.closure (insert a t) = (K ⊔ Subgroup.closure t) ⊔ Subgroup.zpowers a := by
  rw [Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure a,
    sup_comm (Subgroup.closure {a}) (Subgroup.closure t), ← sup_assoc]

theorem gh23_sup_zpowers_dc {G : Type*} [Group G] (K : Subgroup G) {π κ : G} (hπ : π ∈ K)
    (hκ : κ ∈ K) (ρ : G) :
    K ⊔ Subgroup.zpowers (π * ρ * κ) = K ⊔ Subgroup.zpowers ρ := by
  apply le_antisymm
  · apply sup_le le_sup_left
    rw [Subgroup.zpowers_le]
    exact (K ⊔ Subgroup.zpowers ρ).mul_mem
      ((K ⊔ Subgroup.zpowers ρ).mul_mem (Subgroup.mem_sup_left hπ)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers ρ)))
      (Subgroup.mem_sup_left hκ)
  · apply sup_le le_sup_left
    rw [Subgroup.zpowers_le]
    have h1 : π * ρ ∈ K ⊔ Subgroup.zpowers (π * ρ * κ) := by
      have := (K ⊔ Subgroup.zpowers (π * ρ * κ)).mul_mem
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers (π * ρ * κ)))
        (Subgroup.mem_sup_left (K.inv_mem hκ))
      simpa only [mul_inv_cancel_right] using this
    have h2 : ρ ∈ K ⊔ Subgroup.zpowers (π * ρ * κ) := by
      have := (K ⊔ Subgroup.zpowers (π * ρ * κ)).mul_mem
        (Subgroup.mem_sup_left (K.inv_mem hπ)) h1
      simpa only [inv_mul_cancel_left] using this
    exact h2

theorem gh23_mem_of_join_closed {G : Type*} [Group G] [Finite G] (𝓜 : Set (Subgroup G))
    (A : Subgroup G) (hjoin : ∀ K ∈ 𝓜, ∀ σ ∈ A, K ⊔ Subgroup.zpowers σ ∈ 𝓜) {H : Subgroup G}
    (hH : H ≤ A) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓜) (h0 : K₀ ≤ H) : H ∈ 𝓜 := by
  classical
  haveI := Fintype.ofFinite G
  have key : ∀ t : Finset G, ((t : Set G) ⊆ (H : Set G)) →
      K₀ ⊔ Subgroup.closure (t : Set G) ∈ 𝓜 := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · intro _
      simpa using hK₀
    · intro a t ha ih hsub
      rw [Finset.coe_insert] at hsub
      have haH : a ∈ H := hsub (Set.mem_insert a (t : Set G))
      have htH : (t : Set G) ⊆ (H : Set G) :=
        fun x hx => hsub (Set.mem_insert_of_mem a hx)
      have hmem : K₀ ⊔ Subgroup.closure (t : Set G) ∈ 𝓜 := ih htH
      have hj : (K₀ ⊔ Subgroup.closure (t : Set G)) ⊔ Subgroup.zpowers a ∈ 𝓜 :=
        hjoin (K₀ ⊔ Subgroup.closure (t : Set G)) hmem a (hH haH)
      rw [Finset.coe_insert, sup_closure_insert]
      exact hj
  have hfin : ((Finset.univ.filter (· ∈ H) : Finset G) : Set G) = (H : Set G) := by
    ext x
    simp
  have hkey := key (Finset.univ.filter (· ∈ H)) (by rw [hfin])
  rw [hfin, Subgroup.closure_eq, sup_eq_right.2 h0] at hkey
  exact hkey

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
