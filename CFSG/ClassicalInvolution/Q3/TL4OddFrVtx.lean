module

public import CFSG.ClassicalInvolution.Q3.TL4OddBasic

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Lemma52Proof
open CFSG.ClassicalInvolution.Balance

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem hyp51At_of_moved {B : Subgroup G} (hB2 : ∀ b ∈ B, b * b = 1)
    (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) {c : G}
    (hU : ∃ x ∈ modOdd c B, x ∉ modOdd c (Subgroup.zpowers c) ∧
      ∀ L₁ L₂ : Subgroup (OddQuot c), CFSG.IsComponent L₁ → CFSG.IsComponent L₂ →
        (∃ y ∈ L₁, x * y ≠ y * x) → (∃ y ∈ L₂, x * y ≠ y * x) → L₁ = L₂)
    (hO : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L → MovedByAll B c L →
      ∀ x ∈ modOdd c B, x ∈ Subgroup.normalizer (L : Set (OddQuot c)) →
      (∃ y ∈ L, x * y ≠ y * x) → Q3NM.AutOddFreeOn ↥L (IsInducedAut L x)) :
    Hyp51At B c := by
  obtain ⟨x₀, hx₀B, hx₀c, huniq⟩ := hU
  refine ⟨fun L₁ L₂ hL₁ hL₂ hm₁ hm₂ =>
    huniq L₁ L₂ hL₁ hL₂ (hm₁ x₀ hx₀B hx₀c) (hm₂ x₀ hx₀B hx₀c), fun L hL hm => ?_⟩
  have hcomm : ∀ x ∈ modOdd c B, ∀ w ∈ modOdd c B, x * w = w * x := by
    rintro _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hBc _ (Subgroup.mem_subgroupOf.mp hk) _ (Subgroup.mem_subgroupOf.mp hk'))
  have hN : ∀ x ∈ modOdd c B, x ∈ Subgroup.normalizer (L : Set (OddQuot c)) := by
    intro x hx
    have hcomp : CFSG.IsComponent (conjSub x L) :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj x) hL
    have hm' : ∃ y ∈ conjSub x L, x₀ * y ≠ y * x₀ := by
      obtain ⟨y, hy, hne⟩ := hm x₀ hx₀B hx₀c
      refine ⟨x * y * x⁻¹, conj_mem_conjSub hy, fun h => hne ?_⟩
      have hxx₀ := hcomm x hx x₀ hx₀B
      have e1 : x₀ * (x * y * x⁻¹) = x * (x₀ * y) * x⁻¹ := by
        calc x₀ * (x * y * x⁻¹) = (x₀ * x) * y * x⁻¹ := by group
          _ = (x * x₀) * y * x⁻¹ := by rw [← hxx₀]
          _ = x * (x₀ * y) * x⁻¹ := by group
      have e2 : x * y * x⁻¹ * x₀ = x * (y * x₀) * x⁻¹ := by
        have hx₀x : x₀ * x⁻¹ = x⁻¹ * x₀ := by
          calc x₀ * x⁻¹ = x⁻¹ * (x * x₀) * x⁻¹ := by group
            _ = x⁻¹ * (x₀ * x) * x⁻¹ := by rw [hxx₀]
            _ = x⁻¹ * x₀ := by group
        calc x * y * x⁻¹ * x₀ = x * y * (x⁻¹ * x₀) := by group
          _ = x * y * (x₀ * x⁻¹) := by rw [hx₀x]
          _ = x * (y * x₀) * x⁻¹ := by group
      rw [e1, e2] at h
      exact mul_left_cancel (mul_right_cancel h)
    have heq := huniq (conjSub x L) L hcomp hL hm' (hm x₀ hx₀B hx₀c)
    exact LocalBalance.mem_normalizer_of_conjSub_eq heq
  refine Q3NM.alphaOf_eq_bot_of_on L (fun σ => ∃ x ∈ modOdd c B,
      ∃ _ : x ∈ Subgroup.normalizer (L : Set (OddQuot c)),
        (∃ y ∈ L, x * y ≠ y * x) ∧ IsInducedAut L x σ) ?_ _ ?_ ?_ ?_
  · intro 𝒳 hinn f hf hf2
    obtain ⟨x, hx, hxN, hmv, hind⟩ := hf
    exact hO L hL hm x hx hxN hmv 𝒳 hinn f hind hf2
  · rintro _ ⟨w, hw, rfl⟩
    have hw' : (w : OddQuot c) ∈ modOdd c B := Subgroup.mem_subgroupOf.mp hw
    have hww : w * w = 1 := by
      apply Subtype.ext
      obtain ⟨k, hk, hkw⟩ := hw'
      have hkk : k * k = 1 := Subtype.ext (hB2 _ (Subgroup.mem_subgroupOf.mp hk))
      show (w : OddQuot c) * w = 1
      rw [← hkw, ← map_mul, hkk, map_one]
    rw [← map_mul, hww, map_one]
  · obtain ⟨y, hy, hne⟩ := hm x₀ hx₀B hx₀c
    exact ⟨toInducedAutOn L ⟨x₀, hN x₀ hx₀B⟩,
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx₀B),
      toInducedAutOn_ne_one_of_moved L _ hy hne⟩
  · rintro _ ⟨w, hw, rfl⟩ hw1
    have hw' : (w : OddQuot c) ∈ modOdd c B := Subgroup.mem_subgroupOf.mp hw
    refine ⟨w, hw', w.2, ?_, fun y => rfl⟩
    by_contra hcon
    push Not at hcon
    exact hw1 (toInducedAutOn_eq_one_of_commute L w.2 hcon)

end CFSG.ClassicalInvolution.Q3.TL4
