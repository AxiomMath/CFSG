module

public import CFSG.LieType.OutStructureSevenOneSevenHolds
public import CFSG.LieType.OutStructureSevenOneThree

public section

namespace CFSG.LieType.OutStructureFull

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms

section Certificates

theorem sevenOneThree_holds_of
    (hSecond : ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
      ∀ p : ℕ, p.Prime → p ≠ 2 → 5 ≤ p →
      ∀ (L : Subgroup X), L.Normal → CFSG.IsComponent L →
      CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2 →
        CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
          (L ⊔ Subgroup.centralizer (L : Set X)))
    (hThird : ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
      ∀ p : ℕ, p.Prime → p ≠ 2 → 5 ≤ p →
      ∀ (L : Subgroup X), L.Normal → CFSG.IsComponent L →
      CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3 →
        CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
          (L ⊔ Subgroup.centralizer (L : Set X))) :
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneThree := by
  intro X _ _ hK p hp hp2 L hL hLn hcases
  rcases hcases with h1 | h2 | h3
  · exact CFSG.LieType.OutStructure.sevenOneThree_pClosed_of_pRank_le_one
      hK hp hp2 hL hLn h1.le
  · rcases eq_or_ne p 3 with rfl | hp3
    · exact CFSG.LieType.OutStructure.sevenOneThree_rankLeTwo_three hK hL hLn h2
    · have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
      exact hSecond X hK p hp hp2 hp5 L hLn hL h2
  · rcases eq_or_ne p 3 with rfl | hp3
    · exact OutStructure.sevenOneThree_threeRank_three_of_sevenOneSeven
        OutStructure.sevenOneSeven_holds hK hL hLn h3
    · have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
      exact hThird X hK p hp hp2 hp5 L hLn hL h3

end Certificates

end CFSG.LieType.OutStructureFull
