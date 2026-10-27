module

public import CFSG.LieType.Chevalley.CLSEvenE6GraphInvolutionFourGroup
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.C3.Layer1.Thm1End
public import CFSG.GroupTheory.ABGLocalTools.FixedPointCount
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1L3Uniq

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1

theorem four_dvd_card_of_isQuasisimple {Q : Type} [Group Q] [Finite Q]
    (hq : CFSG.IsQuasisimple Q) : 4 ∣ Nat.card Q := by
  obtain ⟨-, hS, hnc⟩ := hq
  have : IsSimpleGroup (Q ⧸ center Q) := hS
  have h2 := CFSG.LieType.Chevalley.two_le_pRank_of_isSimpleGroup (S := Q ⧸ center Q) hnc
  obtain ⟨A, -, hA⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank h2
  have h4 : 4 ∣ Nat.card (Q ⧸ center Q) := hA ▸ Subgroup.card_subgroup_dvd_card A
  exact h4.trans (Subgroup.card_quotient_dvd_card _)

end CFSG.GH74.GLS.C3.Layer1.Thm1L3Uniq
