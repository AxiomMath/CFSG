module

public import CFSG.LargeExtraspecial.AS35CSmith
public import CFSG.LargeExtraspecial.AS35Core

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

@[expose] def AschbacherHypCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), 4 ≤ S.width →
    (5 ≤ S.width ∨ S.MbarTwoBound 7) →
    (∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) → S.AschbacherHyp →
      ∀ g₁ g₂ : G, orderOf (g₁ * S.z * g₁⁻¹ * (g₂ * S.z * g₂⁻¹)) ∈ ({1, 2, 3} : Set ℕ)

theorem aschbacherThreeTranspositionCore_of_smith (h65 : SmithSixFiveStmt)
    (hA : AschbacherHypCore) : AschbacherThreeTranspositionCore := by
  intro G _ _ _ S hn hP hW
  exact hA G S hn hP hW (h65 G S (by omega) hW)

theorem aschbacherThreeTranspositionCore_of_residuals (h63 : SmithSixThreeInput)
    (h64 : SmithSixFourInput) (hA : AschbacherHypCore) : AschbacherThreeTranspositionCore :=
  aschbacherThreeTranspositionCore_of_smith (smithSixFiveStmt_of h63 h64) hA

end CFSG.LargeExtraspecial.S14
