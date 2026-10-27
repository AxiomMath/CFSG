module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup

theorem card_modEq_card_inf_centralizer {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ}
    [Fact p.Prime] {P A : Subgroup Γ} (hP : IsPGroup p P)
    (hPA : ∀ x ∈ P, ∀ a ∈ A, x * a * x⁻¹ ∈ A) :
    Nat.card A ≡ Nat.card (A ⊓ centralizer (P : Set Γ) : Subgroup Γ) [MOD p] := by
  let _ : MulAction P A :=
    { smul := fun x a => ⟨x * a * x⁻¹, hPA x x.2 a a.2⟩
      one_smul := fun a => Subtype.ext (by
        change ((1 : P) : Γ) * a * ((1 : P) : Γ)⁻¹ = a
        simp)
      mul_smul := fun x y a => Subtype.ext (by
        change (x * y : Γ) * a * (x * y : Γ)⁻¹ = x * (y * a * (y : Γ)⁻¹) * (x : Γ)⁻¹
        group) }
  have h := hP.card_modEq_card_fixedPoints A
  have e : MulAction.fixedPoints P A ≃ (A ⊓ centralizer (P : Set Γ) : Subgroup Γ) :=
    { toFun := fun a => ⟨a.1.1, mem_inf.2 ⟨a.1.2, mem_centralizer_iff.2 fun x hx => by
        have h1 : (⟨x, hx⟩ : P) • a.1 = a.1 := a.2 ⟨x, hx⟩
        have h2 : x * a.1.1 * x⁻¹ = a.1.1 := congrArg Subtype.val h1
        calc x * a.1.1 = x * a.1.1 * x⁻¹ * x := by group
          _ = a.1.1 * x := by rw [h2]⟩⟩
      invFun := fun a => ⟨⟨a.1, (mem_inf.1 a.2).1⟩, fun x => Subtype.ext (by
        change (x : Γ) * a.1 * (x : Γ)⁻¹ = a.1
        rw [(mem_centralizer_iff.1 (mem_inf.1 a.2).2 x x.2), mul_inv_cancel_right])⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rwa [Nat.card_congr e] at h

theorem mem_centralizer_zpowers_iff {Γ : Type*} [Group Γ] {y g : Γ} :
    g ∈ centralizer ((zpowers y : Subgroup Γ) : Set Γ) ↔ y * g = g * y := by
  rw [mem_centralizer_iff]
  refine ⟨fun h => h y (mem_zpowers y), fun h k hk => ?_⟩
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hk
  exact (Commute.zpow_left (h : Commute y g) n).eq

end CFSG.LocalAnalysis.EvenBN.Tits
