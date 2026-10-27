module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma18
public import CFSG.GH74.GLS.IVK.Statements.Sec1

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG.GH74.GLS.IVK CFSG.GorensteinWalter

@[expose] def IVK_1_8_iii : Prop :=
  ∀ (F : Type) [Field F] [Finite F], L2Field F → ∀ (K : Type) [Group K] [Finite K] (_ : K ≃* L2 F),
    ∀ y : K, y ≠ 1 → Odd (orderOf y) → ∃ g : K,
      ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), ringChar F₀ = ringChar F ∧
        Nat.card F₀ ≤ Nat.card F ∧
        Nonempty (↥(Subgroup.closure ({y, g * y * g⁻¹} : Set K)) ≃* L2 F₀)

theorem ivk_1_8_of_iii (h : IVK_1_8_iii) : IVK_1_8 := by
  intro F _ _ hF K _ _ e
  exact ⟨ivk_1_8_i F hF K e, ivk_1_8_ii F hF K e, h F hF K e⟩

end CFSG.GH74.GLS.IVK.Proofs2
