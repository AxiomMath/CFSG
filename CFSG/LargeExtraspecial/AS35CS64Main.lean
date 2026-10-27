module

public import CFSG.LargeExtraspecial.AS35CS64Four
public import CFSG.LargeExtraspecial.AS35CS64Exist
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem exists_four_le_card_inf_Qa [IsSimpleGroup G] (hn : 3 ≤ S.width)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) :
    ∃ h : G, h * S.z * h⁻¹ ∈ S.M ∧ h * S.z * h⁻¹ ≠ S.z ∧ 4 ≤ Nat.card ↥(S.QG ⊓ S.Qa h) := by
  obtain ⟨g, hgM, hgne, t, htQ, htx, ht1⟩ := S.exists_inf_Qa_ne_one hn hW
  exact ⟨g, hgM, hgne, S.four_le_card_inf_Qa hn hW rfl hgM hgne htQ htx ht1⟩

end Setting

namespace S14

theorem smithSixFourInput : SmithSixFourInput :=
  fun _ _ _ _ S hn hW => S.exists_four_le_card_inf_Qa hn hW

end S14

end CFSG.LargeExtraspecial
