module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open scoped commutatorElement

theorem index_two_unique {Γ : Type*} [Group Γ] [Finite Γ] (T R D : Subgroup Γ) (c : Γ)
    (hRT : R ≤ T) (hDT : D ≤ T) (hT : Nat.card T = 2 * Nat.card R) (hD : Nat.card D = Nat.card R)
    (hDsq : ∀ x ∈ D, x * x = 1 ∨ x * x = c)
    (hDcomm : ∀ x ∈ D, ∀ y ∈ D, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = c)
    (hA : ∀ y ∈ T, y ∉ R → (y * y = 1 ∨ y * y = c) →
      2 * Nat.card {x : Γ // x ∈ R ∧ (⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = c)} < Nat.card R) :
    D = R := by
  by_contra hne
  have hnle : ¬ D ≤ R := fun h => hne (Subgroup.eq_of_le_of_card_ge h hD.ge)
  obtain ⟨y, hyD, hyR⟩ := SetLike.not_le_iff_exists.1 hnle
  have hrelT : R.relIndex T = 2 := by
    have h := Subgroup.relIndex_mul_card (H := R) (K := T)
    rw [inf_eq_left.2 hRT, hT] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hrelD : R.relIndex D ≤ 2 := by
    have h := Subgroup.relIndex_le_of_le_right (H := R) hDT (by omega)
    omega
  have hcard : Nat.card D ≤ 2 * Nat.card (R ⊓ D : Subgroup Γ) := by
    rw [← Subgroup.relIndex_mul_card (H := R) (K := D)]
    exact Nat.mul_le_mul_right _ hrelD
  let ι : (R ⊓ D : Subgroup Γ) → {x : Γ // x ∈ R ∧ (⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = c)} := fun x =>
    ⟨x.1, (Subgroup.mem_inf.1 x.2).1, hDcomm _ (Subgroup.mem_inf.1 x.2).2 y hyD⟩
  have hι : Function.Injective ι := fun x x' h => by
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  have hle := Nat.card_le_card_of_injective ι hι
  have hlt := hA y (hDT hyD) hyR (hDsq y hyD)
  omega

end CFSG.EvenSporadicStandard.M12Std.Yosh
