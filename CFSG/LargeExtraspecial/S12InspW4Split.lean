module

public import CFSG.LargeExtraspecial.S12InspSplit

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions CFSG.Open

@[expose] def InspW4Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O),
    g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ≠ S.z → S.width = 4 → t ∈ S.Lbar g →
    IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 → S.S12Standing g t → ¬ S.IsReducible12 →
    ((S.IsNondeg12 g ∧ CFSG.Timmesfeld.Outcome (S.Xbar12 g)) ∨
      (¬ S.IsNondeg12 g ∧
        S12FischerConclusion (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g))) →
    S.S12Case1 g t ∨ (S.IsNondeg12 g ∧ S.S12Case2 g t) ∨ S.S12IndexCert g ∨
      (¬ S.IsNondeg12 g ∧ S.S12FuseCert g t) ∨ S.S12GenCert g ∨ Nat.card (S.Lbar g) ≤ 4 ∨
      S.S12SpSixSpin g

theorem timmesfeld12_3InspectionInput_of_split (h4 : InspW4Input) (h5 : Insp5Input) :
    Timmesfeld12_3InspectionInput := by
  intro G _ _ _ S g t haQ hne hn
  rcases Nat.lt_or_ge S.width 5 with hlt | h5'
  · exact h4 G S g t haQ hne (by omega)
  · exact h5 G S g t haQ hne h5'

end CFSG.LargeExtraspecial
