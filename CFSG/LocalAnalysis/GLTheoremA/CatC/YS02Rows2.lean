module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS02Rows
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp6
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU4E6
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Yardstones.Md0ec50421ce4

section Certs

theorem kdLieRowsRest_of_rest2
    (h : KDLieRowSp4Eight ∧ KDLieRowOmega8PlusTwo ∧ KDLieRowG2Eight ∧ KDLieRowTD4Two ∧
        KDLieRowReeF4EightThree ∧ KDLieRowReeF4ThirtyTwoFive) : KDLieRowsRest := by
  obtain ⟨hSp4, hOm8, hG2, hTD4, hR8, hR32⟩ := h
  exact ⟨hSp4, LevelLieSp6.kdLieRowSp6Two_holds, hOm8, hG2, LevelLieU4E.kdLieRowU4Eight_holds,
    kdLieRowU6Two_holds, hTD4, hR8, hR32⟩

end Certs

end CFSG.LocalAnalysis.GLTheoremA
