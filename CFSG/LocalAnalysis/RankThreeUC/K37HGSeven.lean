module

public import CFSG.LocalAnalysis.RankThreeUC.K37HGKit
public import CFSG.LocalAnalysis.GLTheoremB.PiGenSeven
public import CFSG.LocalAnalysis.RankThreeUC.K37HDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37H

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.S15.K37

theorem k37Rest₉_holds : K37Rest₉ := by
  intro X _ _ K E S hs hO
  exfalso
  obtain ⟨-, -, ⟨e⟩⟩ := hO
  haveI : Group.IsPerfect ↥K := hs.quasi.1
  obtain ⟨k, hk⟩ := (k37G_isPGroup_center hs).exists_card_eq
  have hodd : Odd (Nat.card (Subgroup.center ↥K)) := by
    rw [hk]
    exact Odd.pow (by decide : Odd 3)
  exact k37G_false_of_le_centGenI hs
    (CFSG.LocalAnalysis.GLTheoremB.le_centGenI_of_seven (k37G_le_normalizer hs) hs.elem hodd e)

end CFSG.LocalAnalysis.RankThreeUC.S15.K37H

end
