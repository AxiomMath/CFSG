module

public import CFSG.LargeExtraspecial.AS35DSixOne

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

namespace S14

@[expose] def AschbacherWidthTwoResidual : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.width = 2 →
    (∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) →
    (∀ t ∈ S.QG, orderOf t = 2 → S.ZInOTwo t) →
    IsSimpleGroup S.zGen → centralizer (S.zGen : Set G) = ⊥ → S.zGen ⊔ S.QG = ⊤ →
      ∀ g₁ g₂ : G, orderOf (g₁ * S.z * g₁⁻¹ * (g₂ * S.z * g₂⁻¹)) ∈ ({1, 2, 3} : Set ℕ)

@[expose] def AschbacherSecFiveSixResidual : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), AschbacherBelow (Nat.card G) →
    3 ≤ S.width → (∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) →
    (∀ t ∈ S.QG, orderOf t = 2 → S.ZInOTwo t) →
    IsSimpleGroup S.zGen → centralizer (S.zGen : Set G) = ⊥ → S.zGen ⊔ S.QG = ⊤ →
      (∀ g₁ g₂ : G, orderOf (g₁ * S.z * g₁⁻¹ * (g₂ * S.z * g₂⁻¹)) ∈ ({1, 2, 3} : Set ℕ)) ∨
        (S.width = 4 ∧ Nonempty (S.zGen ≃* CFSG.Blueprint.NativeSporadic.Co2))

theorem aschbacherMainStmt_of (hW2 : AschbacherWidthTwoResidual)
    (hR : AschbacherSecFiveSixResidual) : AschbacherMainStmt := by
  refine aschbacherMainStmt_of_step fun G _ _ ih S hn => ?_
  by_contra hS
  obtain ⟨hsimp, hC, htop⟩ := S.sixOne ih hn hS
  have hO : ∀ t ∈ S.QG, orderOf t = 2 → S.ZInOTwo t := fun t ht ht2 =>
    S.zInOTwo_of_not_aschConcl hS ht ht2
  have hW := S.weaklyClosed_of_not_aschConcl hS
  have key : (∀ g₁ g₂ : G, orderOf (g₁ * S.z * g₁⁻¹ * (g₂ * S.z * g₂⁻¹)) ∈ ({1, 2, 3} : Set ℕ)) ∨
      (S.width = 4 ∧ Nonempty (S.zGen ≃* CFSG.Blueprint.NativeSporadic.Co2)) := by
    rcases Nat.lt_or_ge S.width 3 with h | h
    · exact Or.inl (hW2 G S (by omega) hW hO hsimp hC htop)
    · exact hR G S ih h hW hO hsimp hC htop
  refine hS (Or.inr (Or.inl ⟨hsimp, hC, ?_⟩))
  rcases key with h3 | hCo
  · exact Or.inl fun l₁ _ l₂ _ => h3 l₁ l₂
  · exact Or.inr hCo

theorem aschbacherHypCore_of_secFiveSix
    (hW2 : AschbacherWidthTwoResidual) (hR : AschbacherSecFiveSixResidual) :
    AschbacherHypCore :=
  aschbacherHypCore_of_main (aschbacherMainStmt_of hW2 hR)

end S14

end CFSG.LargeExtraspecial
