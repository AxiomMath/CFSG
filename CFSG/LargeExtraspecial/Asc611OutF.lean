module

public import CFSG.LargeExtraspecial.Asc611OutE
public import CFSG.LargeExtraspecial.Asc611OutD

public section

namespace CFSG.LargeExtraspecial.Asc611

open Subgroup Matrix CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ}

theorem add_mem_F2 {a b : K} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    a + b = 0 ∨ a + b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [add_self_K]

section Norm

variable {S : (Fin m → K) → Fin m → K} (hS : SemiInv S) {c x₀ : Fin m → K} (hcS : S c = c)
  (hc : ∀ x, S x = x → herm frob x c = herm frob x x) (hcc : herm frob c c = 0)
include hS hcS hc hcc

omit hc in
theorem fix_iso_add_smul {a : Fin m → K} (haS : S a = a) (ha : herm frob a a = 0) {α : K}
    (hα : α = 0 ∨ α = 1) :
    S (a + α • c) = a + α • c ∧ herm frob (a + α • c) (a + α • c) = 0 := by
  have hαc : S (α • c) = α • c := hS.smul_fix hα hcS
  refine ⟨by rw [hS.add, haS, hαc], ?_⟩
  rw [hS.herm_add_add haS hαc, ha, herm_smul_left, herm_smul_right, hcc, mul_zero, mul_zero,
    add_zero]

theorem herm_add_smul_char {a b : Fin m → K} (haS : S a = a) (ha : herm frob a a = 0)
    (hbS : S b = b) (hb : herm frob b b = 0) (α β : K) :
    herm frob (b + β • c) (a + α • c) = herm frob b a := by
  have hbc : herm frob b c = 0 := by rw [hc b hbS, hb]
  have hca : herm frob c a = 0 := herm_char_left hS hcS hc haS ha
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hbc, hca, hcc]
  ring

theorem IsShape.mul_norm {k₁ k₂ : SUid frob m} {a b : Fin m → K} {α β : K}
    (haS : S a = a) (ha : herm frob a a = 0) (hα : α = 0 ∨ α = 1)
    (hbS : S b = b) (hb : herm frob b b = 0) (hβ : β = 0 ∨ β = 1)
    (h₁ : IsShape S c x₀ (a + α • c) k₁) (h₂ : IsShape S c x₀ (b + β • c) k₂) :
    IsShape S c x₀ ((a + b) + (α + β + herm frob b a) • c) (k₁ * k₂) := by
  obtain ⟨h1S, h1⟩ := fix_iso_add_smul hS hcS hcc haS ha hα
  obtain ⟨h2S, h2⟩ := fix_iso_add_smul hS hcS hcc hbS hb hβ
  have h := IsShape.mul hS hcS hc hcc h₁ h₂ h1S h1 h2S h2
  rw [herm_add_smul_char hS hcS hc hcc haS ha hbS hb] at h
  have e : a + α • c + (b + β • c) + herm frob b a • c =
      (a + b) + (α + β + herm frob b a) • c := by
    module
  rwa [e] at h

end Norm

end CFSG.LargeExtraspecial.Asc611
