module

public import CFSG.GroupTheory.ABGLocalTools.Constraint
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WTail
public import CFSG.Open.GLBDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem exists_normal_order_three_of_tail3 {M C W D : Subgroup G}
    (hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥M)
    (hCn : (C.subgroupOf M).Normal)
    (hCsmall : ∀ E : Subgroup G, E ≤ C → IsPGroup 3 E → Nat.card E ≤ 9)
    (hWM : W ≤ M) (hWp : IsPGroup 3 W) (hWidx : ¬ 3 ∣ (W.subgroupOf M).index)
    (hDW : D ≤ W) (hDC : D ≤ C) (hD9 : Nat.card D = 9)
    (hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hD3 : ∀ d ∈ D, d ^ 3 = 1)
    (hR : ∀ a ∈ W ⊓ Subgroup.centralizer (D : Set G), ∀ b ∈ W ⊓ Subgroup.centralizer (D : Set G),
      a * b = b * a)
    (hA : ∃ A : Subgroup G, A ≤ W ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a ^ 3 = 1) ∧
      Nat.card A = 27)
    (hmax : ∀ A : Subgroup G, A ≤ W → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ a ∈ A, a ^ 3 = 1) → Nat.card A ≤ 27)
    {s : G} (hsM : s ∈ M) (hsD : ∀ d ∈ D, s * d * s⁻¹ ∈ D)
    (hs2 : ∀ d ∈ D, s ^ 2 * d * (s ^ 2)⁻¹ = d⁻¹) :
    ∃ P₀ : Subgroup G, P₀ ≤ M ∧ Nat.card P₀ = 3 ∧
      ((P₀ ⊔ GLBPrimeCore 3 M).subgroupOf M).Normal := by
  obtain ⟨P₀, hP₀W, hP₀3, hP₀n⟩ := exists_normal_order_three_le_of_tail3 hcon hCn hCsmall hWM hWp
    hWidx hDW hDC hD9 hDab hD3 hR hA hmax hsM hsD hs2
  exact ⟨P₀, hP₀W.trans hWM, hP₀3, hP₀n⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
