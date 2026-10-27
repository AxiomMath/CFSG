module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.PGrp

open Subgroup

variable {G : Type*} [Group G]

theorem exists_mul_of_mem_sup_of_le_normalizer {A B : Subgroup G}
    (hAB : A ≤ normalizer (B : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hconj : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B := fun a ha b hb =>
    (mem_normalizer_iff.1 (hAB ha) b).1 hb
  have hconj' : ∀ a ∈ A, ∀ b ∈ B, a⁻¹ * b * a ∈ B := fun a ha b hb =>
    (mem_normalizer_iff''.1 (hAB ha) b).1 hb
  obtain ⟨S, hS⟩ : ∃ S : Subgroup G, ∀ y, y ∈ S ↔ ∃ a ∈ A, ∃ b ∈ B, y = a * b := by
    refine ⟨{ carrier := {y | ∃ a ∈ A, ∃ b ∈ B, y = a * b}
              mul_mem' := ?_
              one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one (1 : G)).symm⟩
              inv_mem' := ?_ }, fun _ => Iff.rfl⟩
    · rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
      exact ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, a₂⁻¹ * b₁ * a₂ * b₂,
        B.mul_mem (hconj' a₂ ha₂ b₁ hb₁) hb₂, by simp only [mul_assoc, mul_inv_cancel_left]⟩
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      exact ⟨a⁻¹, A.inv_mem ha, a * b⁻¹ * a⁻¹, hconj a ha b⁻¹ (B.inv_mem hb),
        by simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]⟩
  have hle : A ⊔ B ≤ S :=
    sup_le (fun a ha => (hS a).2 ⟨a, ha, 1, B.one_mem, (mul_one a).symm⟩)
      (fun b hb => (hS b).2 ⟨1, A.one_mem, b, hb, (one_mul b).symm⟩)
  obtain ⟨a, ha, b, hb, h⟩ := (hS x).1 (hle hx)
  exact ⟨a, ha, b, hb, h⟩

theorem card_sup_mul_card_inf [Finite G] {A B : Subgroup G}
    (hAB : A ≤ normalizer (B : Set G)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have hBN : B ≤ normalizer (B : Set G) := Subgroup.le_normalizer
  have hCN : A ⊔ B ≤ normalizer (B : Set G) := sup_le hAB hBN
  have key : B.relIndex (A ⊔ B) = (A ⊓ B).relIndex A := by
    rw [Subgroup.inf_relIndex_left, ← Subgroup.relIndex_subgroupOf hCN,
      ← Subgroup.relIndex_subgroupOf hAB, Subgroup.subgroupOf_sup hAB hBN,
      Subgroup.relIndex_sup_right]
  have hC : B.relIndex (A ⊔ B) * Nat.card ↥B = Nat.card ↥(A ⊔ B) := by
    have h := Subgroup.relIndex_mul_card (H := B) (K := A ⊔ B)
    rwa [inf_eq_left.2 (le_sup_right : B ≤ A ⊔ B)] at h
  have hA : (A ⊓ B).relIndex A * Nat.card ↥(A ⊓ B) = Nat.card ↥A := by
    have h := Subgroup.relIndex_mul_card (H := A ⊓ B) (K := A)
    rwa [inf_eq_left.2 (inf_le_left : A ⊓ B ≤ A)] at h
  calc Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B)
      = (B.relIndex (A ⊔ B) * Nat.card ↥B) * Nat.card ↥(A ⊓ B) := by rw [hC]
    _ = ((A ⊓ B).relIndex A * Nat.card ↥(A ⊓ B)) * Nat.card ↥B := by rw [key]; ring
    _ = Nat.card ↥A * Nat.card ↥B := by rw [hA]

theorem isPGroup_sup_of_le_normalizer [Finite G] {p : ℕ} [Fact p.Prime] {A B : Subgroup G}
    (hA : IsPGroup p ↥A) (hB : IsPGroup p ↥B) (hAB : A ≤ normalizer (B : Set G)) :
    IsPGroup p ↥(A ⊔ B) :=
  IsPGroup.to_sup_of_normal_right' hA hB hAB

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.PGrp

end
