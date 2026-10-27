module

import CFSG.LocalAnalysis.OddStandard.GlueAlt
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.RouteWAlt
public import CFSG.LocalAnalysis.OddStandard.RouteWChildren
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdDefs

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem childLargeAltW_of_inputsStd
    (hStd : AlternatingStandardFormInputW)
    (hW : Solomon75.Solomon2AnStdW) : ChildLargeAltW := by
  intro G _ _ L hS hn
  obtain ⟨n, hn8, ⟨e⟩⟩ := hn
  have hq : CFSG.IsQuasisimple L :=
    (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hS.standard.1
  have : Group.IsPerfect L := hq.1
  have hZ : Nat.card (center L) ≤ 2 := GlueAlt.card_center_le_two_of_alt hn8 e
  have hpos : 0 < Nat.card (center L) := Nat.card_pos
  rcases (show Nat.card (center L) = 1 ∨ Nat.card (center L) = 2 by omega) with h1 | h2
  ·
    have hbot : center L = ⊥ := Subgroup.card_eq_one.1 h1
    let eL : L ≃* L ⧸ center L :=
      MulEquiv.ofBijective (QuotientGroup.mk' (center L))
        ⟨(MonoidHom.ker_eq_bot_iff _).1 (by rw [QuotientGroup.ker_mk']; exact hbot),
          QuotientGroup.mk'_surjective _⟩
    have := hS.simple
    rcases hStd G hS.nonab hS.kProper L n
      (GlueAlt.isStandardSubgroup_of_standardComponentIsStandard hS.standard) hn8
      ⟨eL.trans e⟩ with ⟨⟨eG⟩⟩ | hlie
    · exact Or.inl ⟨n + 4, by omega, ⟨eG⟩⟩
    · exact Or.inr (Or.inl hlie)
  ·
    exact hW G L hS n hn8 ⟨e⟩ h2

end CFSG.OddStandard
