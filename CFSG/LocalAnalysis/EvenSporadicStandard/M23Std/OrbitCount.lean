module

public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup

variable {G : Type} [Group G]

theorem card_le_mul_card_centralizer [Finite G] {H W : Subgroup G} {y : G}
    (hmap : ∀ r ∈ H, y⁻¹ * (r * y * r⁻¹) ∈ W) :
    Nat.card H ≤ Nat.card W * Nat.card ↥(H ⊓ centralizer ({y} : Set G)) := by
  set C := H ⊓ centralizer ({y} : Set G) with hC
  set C' : Subgroup ↥H := C.subgroupOf H with hC'
  have hCH : C ≤ H := inf_le_left
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup C'
  have h2 : Nat.card C' = Nat.card C := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCH).toEquiv
  have h3 : Nat.card (↥H ⧸ C') ≤ Nat.card W := by
    refine Nat.card_le_card_of_injective
      (Quotient.lift (s := QuotientGroup.leftRel C')
        (fun r : ↥H => (⟨y⁻¹ * ((r : G) * y * (r : G)⁻¹), hmap r r.2⟩ : ↥W)) ?_) ?_
    · intro a b hab
      have hab' : a⁻¹ * b ∈ C' := (QuotientGroup.leftRel_apply).1 hab
      have hab'' : ((a⁻¹ * b : ↥H) : G) ∈ centralizer ({y} : Set G) :=
        (mem_inf.1 (Subgroup.mem_subgroupOf.1 hab')).2
      have hcomm : (a : G)⁻¹ * (b : G) * y = y * ((a : G)⁻¹ * (b : G)) :=
        (mem_centralizer_singleton_iff.1 hab'').symm.symm
      apply Subtype.ext
      show y⁻¹ * ((a : G) * y * (a : G)⁻¹) = y⁻¹ * ((b : G) * y * (b : G)⁻¹)
      have : (a : G) * y * (a : G)⁻¹ = (b : G) * y * (b : G)⁻¹ := by
        calc (a : G) * y * (a : G)⁻¹ = (a : G) * (y * ((a : G)⁻¹ * (b : G))) * (b : G)⁻¹ := by
              group
          _ = (a : G) * (((a : G)⁻¹ * (b : G)) * y) * (b : G)⁻¹ := by rw [← hcomm]
          _ = (b : G) * y * (b : G)⁻¹ := by group
      rw [this]
    · intro q₁ q₂ h
      induction q₁ using Quotient.inductionOn with
      | h a =>
        induction q₂ using Quotient.inductionOn with
        | h b =>
          have h' : y⁻¹ * ((a : G) * y * (a : G)⁻¹) = y⁻¹ * ((b : G) * y * (b : G)⁻¹) :=
            congrArg Subtype.val h
          have h'' : (a : G) * y * (a : G)⁻¹ = (b : G) * y * (b : G)⁻¹ := mul_left_cancel h'
          apply Quotient.sound
          refine (QuotientGroup.leftRel_apply).2 (Subgroup.mem_subgroupOf.2 (mem_inf.2 ⟨?_, ?_⟩))
          · exact (a⁻¹ * b : ↥H).2
          · refine mem_centralizer_singleton_iff.2 ?_
            show (a : G)⁻¹ * (b : G) * y = y * ((a : G)⁻¹ * (b : G))
            have : (b : G) * y * (b : G)⁻¹ = (a : G) * y * (a : G)⁻¹ := h''.symm
            calc (a : G)⁻¹ * (b : G) * y = (a : G)⁻¹ * ((b : G) * y * (b : G)⁻¹) * (b : G) := by
                  group
              _ = (a : G)⁻¹ * ((a : G) * y * (a : G)⁻¹) * (b : G) := by rw [this]
              _ = y * ((a : G)⁻¹ * (b : G)) := by group
  calc Nat.card H = Nat.card (↥H ⧸ C') * Nat.card C' := h1
    _ ≤ Nat.card W * Nat.card C := by rw [h2]; exact Nat.mul_le_mul_right _ h3

end CFSG.EvenSporadicStandard.M23Std
