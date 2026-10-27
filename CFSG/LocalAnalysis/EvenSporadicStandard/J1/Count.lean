module

public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace CFSG.EvenSporadicStandard.J1Std

open Subgroup

variable {G : Type} [Group G]

theorem card_eq_card_conjClass_mul (M : Subgroup G) (z : G) :
    Nat.card M = Nat.card {x : G // ∃ m ∈ M, x = m * z * m⁻¹} *
      Nat.card (centralizer ({z} : Set G) ⊓ M : Subgroup G) := by
  set K : Subgroup M := (centralizer ({z} : Set G) ⊓ M).subgroupOf M with hK
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup K
  have h2 : Nat.card K = Nat.card (centralizer ({z} : Set G) ⊓ M : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have key : ∀ a b : M, a⁻¹ * b ∈ K ↔ (a : G) * z * (a : G)⁻¹ = (b : G) * z * (b : G)⁻¹ := by
    intro a b
    rw [hK, mem_subgroupOf, Subgroup.mem_inf, mem_centralizer_singleton_iff]
    obtain ⟨g, hg⟩ : ∃ g : G, g = (a : G)⁻¹ * b := ⟨_, rfl⟩
    have hb : (b : G) = a * g := by rw [hg]; group
    have hgm : ((a⁻¹ * b : M) : G) = g := by rw [hg]; rfl
    rw [hgm, hb]
    refine ⟨fun e => ?_, fun e => ⟨?_, by rw [hg]; exact (a⁻¹ * b).2⟩⟩
    · have e2 : g * z * g⁻¹ = z := by
        calc g * z * g⁻¹ = (z * g) * g⁻¹ := by rw [e.1]
          _ = z := by group
      calc (a : G) * z * (a : G)⁻¹ = (a : G) * (g * z * g⁻¹) * (a : G)⁻¹ := by rw [e2]
        _ = (a * g) * z * (a * g)⁻¹ := by group
    · have e2 : g * z * g⁻¹ = z := by
        calc g * z * g⁻¹ = (a : G)⁻¹ * ((a * g) * z * (a * g)⁻¹) * a := by group
          _ = (a : G)⁻¹ * (a * z * (a : G)⁻¹) * a := by rw [← e]
          _ = z := by group
      calc g * z = (g * z * g⁻¹) * g := by group
        _ = z * g := by rw [e2]
  have h3 : Nat.card (M ⧸ K) = Nat.card {x : G // ∃ m ∈ M, x = m * z * m⁻¹} := by
    refine Nat.card_congr (Equiv.ofBijective (Quotient.lift (fun m : M =>
      (⟨m * z * m⁻¹, m, m.2, rfl⟩ : {x : G // ∃ m ∈ M, x = m * z * m⁻¹})) ?_) ⟨?_, ?_⟩)
    · intro a b hab
      exact Subtype.ext ((key a b).1 (QuotientGroup.leftRel_apply.1 hab))
    · intro x y hxy
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      exact QuotientGroup.eq.2 ((key a b).2 (congrArg Subtype.val hxy))
    · rintro ⟨x, m, hm, rfl⟩
      exact ⟨QuotientGroup.mk ⟨m, hm⟩, rfl⟩
  rw [h2, h3] at h1
  exact h1


theorem zpow_eq_one_or_self {y : G} (hy : y * y = 1) (n : ℤ) : y ^ n = 1 ∨ y ^ n = y := by
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left
    rw [← Int.emod_add_mul_ediv n 2, h, zpow_add, zpow_mul]
    simp [pow_two, hy]
  · right
    rw [← Int.emod_add_mul_ediv n 2, h, zpow_add, zpow_mul]
    simp [pow_two, hy]

end CFSG.EvenSporadicStandard.J1Std
