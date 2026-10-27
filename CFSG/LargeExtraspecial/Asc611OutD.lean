module

public import CFSG.LargeExtraspecial.Asc611OutC

public section

namespace CFSG.LargeExtraspecial.Asc611

open Subgroup Matrix CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ}

@[expose] def IsShape (S : (Fin m → K) → Fin m → K) (c x₀ z : Fin m → K) (k : SUid frob m) :
    Prop :=
  (∀ v, S v = v → herm frob v v = 0 → k • v = v + herm frob v z • c) ∧ k • x₀ = x₀ + z

section Shape

variable {S : (Fin m → K) → Fin m → K} (hS : SemiInv S) {c x₀ : Fin m → K} (hcS : S c = c)
  (hc : ∀ x, S x = x → herm frob x c = herm frob x x) (hcc : herm frob c c = 0)
  (hx₀S : S x₀ = x₀) (hx₀ : herm frob x₀ x₀ = 1)
include hS hcS hc hcc

omit hcc in
theorem herm_char_left {v : Fin m → K} (hvS : S v = v) (hv : herm frob v v = 0) :
    herm frob c v = 0 := by
  rw [hS.herm_symm hvS hcS, hc v hvS, hv]

theorem IsShape.mul {k₁ k₂ : SUid frob m} {z₁ z₂ : Fin m → K} (h₁ : IsShape S c x₀ z₁ k₁)
    (h₂ : IsShape S c x₀ z₂ k₂) (hz₁S : S z₁ = z₁) (hz₁ : herm frob z₁ z₁ = 0)
    (hz₂S : S z₂ = z₂) (hz₂ : herm frob z₂ z₂ = 0) :
    IsShape S c x₀ (z₁ + z₂ + herm frob z₂ z₁ • c) (k₁ * k₂) := by
  have hk₁c : k₁ • c = c := by
    rw [h₁.1 c hcS hcc, hS.herm_symm hz₁S hcS, hc z₁ hz₁S, hz₁, zero_smul, add_zero]
  refine ⟨fun v hvS hv => ?_, ?_⟩
  · rw [mul_smul, h₂.1 v hvS hv, smul_add, smul_smul_comm, hk₁c, h₁.1 v hvS hv,
      herm_add_right, herm_add_right, herm_smul_right, hc v hvS, hv, mul_zero, add_zero,
      add_smul, add_assoc]
  · rw [mul_smul, h₂.2, smul_add, h₁.2, h₁.1 z₂ hz₂S hz₂]
    abel

theorem isShape_tvU (hx₀S : S x₀ = x₀) (hx₀ : herm frob x₀ x₀ = 1) {w : Fin m → K}
    (hwS : S w = w) (hw : herm frob w w = 0) :
    IsShape S c x₀ (w + (herm frob w x₀ + 1) • c) (tvU (w + c) * tvU w) := by
  have hwc : herm frob (w + c) (w + c) = 0 := by
    rw [hS.herm_add_add hwS hcS, hw, hcc, add_zero]
  have hcw : herm frob c w = 0 := herm_char_left hS hcS hc hwS hw
  refine ⟨fun v hvS hv => ?_, ?_⟩
  · have hcv : herm frob c v = 0 := herm_char_left hS hcS hc hvS hv
    rw [mul_smul, tvU_smul hw, tvU_smul hwc]
    have e1 : herm frob (w + c) (v + herm frob w v • w) = herm frob w v := by
      rw [herm_add_left, herm_add_right, herm_add_right, herm_smul_right, herm_smul_right, hw,
        hcv, hcw]
      ring
    have e2 : herm frob v (w + (herm frob w x₀ + 1) • c) = herm frob w v := by
      rw [herm_add_right, herm_smul_right, hc v hvS, hv, mul_zero, add_zero,
        ← hS.herm_symm hvS hwS]
    rw [e1, e2]
    linear_combination (norm := module) (herm frob w v) • (two_eq_zero • w)
  · have hcx : herm frob c x₀ = 1 := by rw [hS.herm_symm hx₀S hcS, hc x₀ hx₀S, hx₀]
    rw [mul_smul, tvU_smul hw, tvU_smul hwc]
    have e1 : herm frob (w + c) (x₀ + herm frob w x₀ • w) = herm frob w x₀ + 1 := by
      rw [herm_add_left, herm_add_right, herm_add_right, herm_smul_right, herm_smul_right, hw,
        hcx, hcw]
      ring
    rw [e1]
    linear_combination (norm := module) (herm frob w x₀) • (two_eq_zero • w)

theorem IsShape.eq_tvU (hx₀S : S x₀ = x₀) (hx₀ : herm frob x₀ x₀ = 1) {k : SUid frob m}
    (hk : IsShape S c x₀ c k) : k = tvU c := by
  refine hS.eq_of_fix fun x hxS => ?_
  have hcx : herm frob c x = herm frob x x := by rw [hS.herm_symm hxS hcS, hc x hxS]
  rcases herm_self_eq_zero_or_one x with h0 | h1
  · rw [hk.1 x hxS h0, tvU_smul hcc, hc x hxS, hcx, h0, zero_smul]
  · have hfix : S (x + x₀) = x + x₀ := by rw [hS.add, hxS, hx₀S]
    have hiso : herm frob (x + x₀) (x + x₀) = 0 := by
      rw [hS.herm_add_add hxS hx₀S, h1, hx₀, add_self_K]
    have h2 := hk.1 _ hfix hiso
    rw [hc _ hfix, hiso, zero_smul, add_zero, smul_add, hk.2] at h2
    rw [tvU_smul hcc, hcx, h1, one_smul]
    generalize k • x = kx at h2 ⊢
    linear_combination (norm := module) h2 - two_eq_zero • c

end Shape

end CFSG.LargeExtraspecial.Asc611
