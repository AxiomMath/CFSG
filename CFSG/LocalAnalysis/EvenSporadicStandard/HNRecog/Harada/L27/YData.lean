module

public import CFSG.LocalAnalysis.ComponentClassification.SolvableRadical
public import CFSG.Open.Defs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup CFSG.Open

structure FinalData (Y : Type) [Group Y] (P F : Subgroup Y) (v : Y) : Prop where
  free : CFSG.ComponentClassification.SolvableRadical.Free Y
  card_le : Nat.card Y ≤ 16200
  P_iso : Nonempty (P ≃* Equiv.Perm (Fin 5))
  F_iso : Nonempty (F ≃* alternatingGroup (Fin 5))
  v_sq : v * v = 1
  v_ne_one : v ≠ 1
  F_comm : ∀ f ∈ F, f * v = v * f
  centralizer_le : ∀ g : Y, g * v = v * g → g ∈ F ⊔ Subgroup.zpowers v
  nonconj : ∀ x ∈ F, orderOf x = 5 → ∀ p ∈ ⁅P, P⁆, orderOf p = 5 →
    ∀ y : Y, y * x * y⁻¹ ∉ Subgroup.zpowers p

structure TwoA5 (Y : Type) [Group Y] (T₁ T₂ : Subgroup Y) : Prop where
  comp₁ : IsComponentOf T₁ ⊤
  comp₂ : IsComponentOf T₂ ⊤
  ne : T₁ ≠ T₂
  only : ∀ C : Subgroup Y, IsComponentOf C ⊤ → C = T₁ ∨ C = T₂
  card₁ : Nat.card T₁ = 60
  card₂ : Nat.card T₂ = 60

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
