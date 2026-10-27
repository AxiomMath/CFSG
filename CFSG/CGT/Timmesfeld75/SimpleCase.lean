module

public import CFSG.CGT.Timmesfeld75.NodeDerivation
public import CFSG.CGT.Timmesfeld75.WeaklyClosed

public section

namespace CFSG.CGT.Timmesfeld75

@[expose] def SimpleCaseListStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ T : Subgroup G, IsWC T → 4 ≤ Nat.card T → ListGroup G

@[expose] def SimpleCaseStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ T : Subgroup G, IsWC T → 4 ≤ Nat.card T → ListGroup G ∧
      ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ g ∈ Subgroup.normalizer (T : Set G), g * x * g⁻¹ = y

theorem SimpleCaseStmt.list (h : SimpleCaseStmt) : SimpleCaseListStmt :=
  fun G _ _ _ hna T hT h4 => (h G hna T hT h4).1

theorem nodeStatement_of_simpleCase (h : SimpleCaseListStmt) : NodeStatement := by
  intro G _ _ _ hna B hB h4 hTI hWC
  have hB' : IsWC B := isWC_of_corBHyp (corBHyp_of_ti_of_weaklyClosed hB hTI hWC)
  exact h G hna B hB' h4

end CFSG.CGT.Timmesfeld75
