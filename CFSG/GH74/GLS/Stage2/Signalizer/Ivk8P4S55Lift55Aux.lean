module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Tactic.Group

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.Lift55Aux

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

theorem mem_normalizer_commutator {H K : Subgroup G} {y : G}
    (hH : y ∈ normalizer (H : Set G)) (hK : y ∈ normalizer (K : Set G)) :
    y ∈ normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  have key : ∀ z : G, z ∈ normalizer (H : Set G) → z ∈ normalizer (K : Set G) →
      ∀ c ∈ ⁅H, K⁆, z * c * z⁻¹ ∈ ⁅H, K⁆ := by
    intro z hzH hzK c hc
    have hle : ⁅H, K⁆ ≤ ⁅H, K⁆.comap (MulAut.conj z).toMonoidHom := by
      rw [commutator_le]
      intro a ha b hb
      rw [mem_comap]
      change z * ⁅a, b⁆ * z⁻¹ ∈ ⁅H, K⁆
      rw [conjugate_commutatorElement]
      exact commutator_mem_commutator ((mem_normalizer_iff.mp hzH a).mp ha)
        ((mem_normalizer_iff.mp hzK b).mp hb)
    exact hle hc
  rw [mem_normalizer_iff]
  intro c
  refine ⟨key y hH hK c, fun hc => ?_⟩
  have h := key y⁻¹ (inv_mem hH) (inv_mem hK) _ hc
  simpa [mul_assoc] using h

theorem commutator_subgroupOf_of_le {H K L : Subgroup G} (hH : H ≤ L) (hK : K ≤ L) :
    ⁅H, K⁆.subgroupOf L = ⁅H.subgroupOf L, K.subgroupOf L⁆ := by
  apply Subgroup.map_injective L.subtype_injective
  rw [map_commutator, subgroupOf_map_subtype, subgroupOf_map_subtype, subgroupOf_map_subtype,
    inf_eq_left.mpr hH, inf_eq_left.mpr hK, inf_eq_left.mpr (commutator_le_of_le hH hK)]

theorem exists_perfect_of_commutator_closed [Finite G] (P : Subgroup G → Prop)
    (hP : ∀ X, P X → P ⁅X, X⁆) {U : Subgroup G} (hU : P U) : ∃ X, P X ∧ ⁅X, X⁆ = X := by
  suffices h : ∀ n, ∀ X : Subgroup G, Nat.card X = n → P X → ∃ Y, P Y ∧ ⁅Y, Y⁆ = Y from
    h _ U rfl hU
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X hXn hX
    by_cases hXX : ⁅X, X⁆ = X
    · exact ⟨X, hX, hXX⟩
    · have hlt : ⁅X, X⁆ < X := lt_of_le_of_ne (commutator_le_self X) hXX
      exact ih _ (hXn ▸ card_lt_of_lt hlt) _ rfl (hP X hX)

theorem commutator_commutator_zpowers_eq_bot {L N : Subgroup G} {g : G}
    (hLN : L ≤ normalizer (N : Set G)) (hgN : N ≤ centralizer ({g} : Set G)) :
    ⁅⁅L, zpowers g⁆, N⁆ = ⊥ := by
  have hZN : ⁅zpowers g, N⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer, zpowers_le, mem_centralizer_iff]
    intro n hn
    exact ((mem_centralizer_iff.mp (hgN hn)) g (Set.mem_singleton g)).symm
  apply commutator_commutator_eq_bot_of_rotate
  · rw [hZN, commutator_bot_left]
  · have h1 : ⁅N, L⁆ ≤ N := by
      rw [commutator_comm]
      exact le_normalizer_iff_commutator_le_right.mp hLN
    rw [eq_bot_iff]
    calc ⁅⁅N, L⁆, zpowers g⁆ ≤ ⁅N, zpowers g⁆ := commutator_mono h1 le_rfl
      _ = ⊥ := by rw [commutator_comm, hZN]

theorem commutator_sup_le_of_le_centralizer {X A C : Subgroup G}
    (hC : C ≤ centralizer (X : Set G)) (hCA : C ≤ normalizer (A : Set G)) :
    ⁅X, A ⊔ C⁆ ≤ ⁅X, A⁆ := by
  rw [commutator_le]
  intro x hx y hy
  have hy' : y ∈ ((A ⊔ C : Subgroup G) : Set G) := hy
  rw [coe_mul_of_right_le_normalizer_left A C hCA] at hy'
  obtain ⟨a, ha, c, hc, rfl⟩ := Set.mem_mul.mp hy'
  have hxc : Commute c x⁻¹ :=
    Commute.inv_right_iff.mpr ((mem_centralizer_iff.mp (hC hc)) x hx).symm
  have h : ⁅x, a * c⁆ = ⁅x, a⁆ := by
    calc ⁅x, a * c⁆ = x * a * (c * x⁻¹) * c⁻¹ * a⁻¹ := by
          rw [commutatorElement_def]
          group
      _ = x * a * (x⁻¹ * c) * c⁻¹ * a⁻¹ := by rw [hxc.eq]
      _ = ⁅x, a⁆ := by
          rw [commutatorElement_def]
          group
  rw [h]
  exact commutator_mem_commutator hx ha

theorem commutator_top_eq_top {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hQ : ∃ a b : Q, a * b ≠ b * a) : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆) with
    h | h
  · obtain ⟨a, b, hab⟩ := hQ
    exfalso
    apply hab
    have hm := commutator_mem_commutator (mem_top a) (mem_top b)
    rwa [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
  · exact h

theorem map_subgroupOf_normal {Q : Type*} [Group Q] {L K X : Subgroup G} (φ : ↥L →* Q)
    (hX : (X.subgroupOf L).map φ = ⊤) (hXK : X ≤ normalizer (K : Set G)) :
    ((K.subgroupOf L).map φ).Normal := by
  constructor
  intro n hn q
  have hq : q ∈ (X.subgroupOf L).map φ := hX ▸ mem_top q
  obtain ⟨x, hx, rfl⟩ := hq
  obtain ⟨k, hk, rfl⟩ := hn
  refine ⟨x * k * x⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  rw [SetLike.mem_coe, mem_subgroupOf] at hx hk
  rw [SetLike.mem_coe, mem_subgroupOf, coe_mul, coe_mul, coe_inv]
  exact (mem_normalizer_iff.mp (hXK hx) k).mp hk

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.Lift55Aux
