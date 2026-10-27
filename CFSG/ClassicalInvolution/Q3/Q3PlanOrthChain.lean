module

public import CFSG.ClassicalInvolution.Q3.Q3PlanSplit

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open
open scoped MatrixGroups commutatorElement

section Chain

variable {G : Type*} [Group G]

private theorem le_of_isSubnormal_commutator_aux {A Y X : Subgroup G}
    (hX : ∀ x ∈ X, ∃ b, (∀ y ∈ Y, y * b = b * y) ∧ x * b ∈ A) (hY : Y ≤ ⁅X, Y⁆)
    {H K : Subgroup G} (h : IsSubnormal H K) (hYK : Y ≤ K) (hAH : A ≤ H) : Y ≤ H := by
  induction h with
  | refl H => exact hYK
  | @step H M K hHM hN hMK ih =>
    have hYM : Y ≤ M := ih hYK (hAH.trans hHM)
    refine hY.trans (Subgroup.commutator_le.mpr fun x hx y hy => ?_)
    obtain ⟨b, hb, hxb⟩ := hX x hx
    have hxbH : x * b ∈ H := hAH hxb
    have hconj : y * (x * b)⁻¹ * y⁻¹ ∈ H :=
      (Subgroup.normal_subgroupOf_iff hHM).mp hN _ y (H.inv_mem hxbH) (hYM hy)
    have hby : b * y = y * b := (hb y hy).symm
    have : ⁅x, y⁆ = (x * b) * (y * (x * b)⁻¹ * y⁻¹) := by
      calc ⁅x, y⁆ = x * y * x⁻¹ * y⁻¹ := rfl
        _ = x * (y * b) * b⁻¹ * x⁻¹ * y⁻¹ := by group
        _ = x * (b * y) * b⁻¹ * x⁻¹ * y⁻¹ := by rw [hby]
        _ = (x * b) * (y * (x * b)⁻¹ * y⁻¹) := by group
    rw [this]
    exact H.mul_mem hxbH hconj

theorem le_of_isSubnormal_commutator {T A Y X : Subgroup G} (hsub : IsSubnormal A T)
    (hYT : Y ≤ T) (hX : ∀ x ∈ X, ∃ b, (∀ y ∈ Y, y * b = b * y) ∧ x * b ∈ A)
    (hY : Y ≤ ⁅X, Y⁆) : Y ≤ A :=
  le_of_isSubnormal_commutator_aux hX hY hsub hYT le_rfl

end Chain

section SL23

@[expose] def sl2ThreeQ8 : Subgroup SL(2, ZMod 3) where
  carrier := {x | x ^ 4 = 1}
  mul_mem' := by
    intro a b ha hb
    revert a b
    decide +kernel
  one_mem' := one_pow 4
  inv_mem' := by
    intro a ha
    have h4 : a ^ 4 = 1 := ha
    change a⁻¹ ^ 4 = 1
    rw [inv_pow, h4, inv_one]

theorem mem_sl2ThreeQ8 {x : SL(2, ZMod 3)} : x ∈ sl2ThreeQ8 ↔ x ^ 4 = 1 := Iff.rfl

theorem pow_three_mem_sl2ThreeQ8 (g : SL(2, ZMod 3)) : g ^ 3 ∈ sl2ThreeQ8 := by
  have h : ∀ g : SL(2, ZMod 3), (g ^ 3) ^ 4 = 1 := by decide +kernel
  exact h g

theorem exists_commutator_of_mem_sl2ThreeQ8 : ∀ x : SL(2, ZMod 3), x ^ 4 = 1 →
    ∃ g q : SL(2, ZMod 3), q ^ 4 = 1 ∧ x = ⁅g, q⁆ := by
  decide +kernel

theorem sl2ThreeQ8_le_commutator : sl2ThreeQ8 ≤ ⁅(⊤ : Subgroup SL(2, ZMod 3)), sl2ThreeQ8⁆ := by
  intro x hx
  obtain ⟨g, q, hq, rfl⟩ := exists_commutator_of_mem_sl2ThreeQ8 x hx
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) hq

theorem neg_one_cases : ∀ x : SL(2, ZMod 3), x ≠ 1 →
    x ^ 3 = 1 ∨ x = -1 ∨ x ^ 2 = -1 ∨ x ^ 3 = -1 := by
  decide +kernel

theorem eq_neg_one_of_sq_eq_one : ∀ x : SL(2, ZMod 3), x ^ 2 = 1 → x = 1 ∨ x = -1 := by
  decide +kernel

variable {G : Type*} [Group G]

theorem neg_one_mem_of_normal {A N : Subgroup G} (e : SL(2, ZMod 3) ≃* A) (hNA : N ≤ A)
    (hN : ∀ g ∈ A, ∀ n ∈ N, g * n * g⁻¹ ∈ N) {n : G} (hn : n ∈ N) (hn1 : n ≠ 1) :
    ((e (-1) : A) : G) ∈ N := by
  obtain ⟨x, hx⟩ := e.surjective ⟨n, hNA hn⟩
  have hxn : ((e x : A) : G) = n := congrArg Subtype.val hx
  have hx1 : x ≠ 1 := fun h => hn1 (by rw [← hxn, h, map_one]; rfl)
  have hmul : ∀ {a b : G}, a ∈ N → b ∈ N → a * b ∈ N := fun ha hb => N.mul_mem ha hb
  have hpow : ∀ k : ℕ, ((e x : A) : G) ^ k = ((e (x ^ k) : A) : G) := fun k => by
    rw [map_pow]
    rfl
  rcases neg_one_cases x hx1 with h3 | h | h | h
  ·
    have hN' : ∀ y ∈ N.subgroupOf A, ∀ g : A, g * y * g⁻¹ ∈ N.subgroupOf A := fun y hy g => by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      exact hN g g.2 y hy
    have hx' : (e x : A) ∈ N.subgroupOf A := by
      rw [Subgroup.mem_subgroupOf]
      rw [hxn]
      exact hn
    have hx3 : (e x : A) ^ 3 = 1 := by rw [← map_pow, h3, map_one]
    have hx1' : (e x : A) ≠ 1 := fun h' => hx1 (e.injective (by rw [h', map_one]))
    have htop := eq_top_of_normal_of_pow_three e hN' hx' hx3 hx1'
    have : (e (-1) : A) ∈ N.subgroupOf A := htop ▸ Subgroup.mem_top _
    exact this
  · have : ((e (-1) : A) : G) = n := by rw [← h]; exact hxn
    rw [this]
    exact hn
  · have h2 : ((e x : A) : G) ^ 2 ∈ N := by
      rw [pow_two]
      exact hmul (hxn ▸ hn) (hxn ▸ hn)
    rw [hpow, h] at h2
    exact h2
  · have h2 : ((e x : A) : G) ^ 3 ∈ N := by
      rw [pow_succ, pow_two]
      exact hmul (hmul (hxn ▸ hn) (hxn ▸ hn)) (hxn ▸ hn)
    rw [hpow, h] at h2
    exact h2

end SL23

end CFSG.ClassicalInvolution.Q3
