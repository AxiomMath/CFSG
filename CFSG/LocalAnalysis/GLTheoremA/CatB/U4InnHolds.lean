module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnU5
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnU48
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnU6f
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnSp8d
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnD4d

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem isTableU4_not_two {i : TauCeti.CFSGIndex} (h : S9.isTableU4 i ∧ ¬ S9.isU4two i) :
    S9.isD4two i ∨ S9.isSp8two i ∨ S9.isU4eight i ∨ S9.isU5two i ∨ S9.isU6two i := by
  obtain ⟨hT, hn4⟩ := h
  unfold S9.isTableU4 at hT
  rcases hT with h1 | h1 | h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h1)))
  · exact absurd h1 hn4

theorem u4InnRest_of_rows (hD4 : U4InnAt S9.isD4two) (hSp : U4InnAt S9.isSp8two) :
    U4InnRest :=
  u4InnRest_of_main (U4InnAt.mono (fun _ hi => isTableU4_not_two hi)
    (hD4.of_or (hSp.of_or (u4InnAt_u4eight.of_or (u4InnAt_u5two.of_or u4InnAt_u6two)))))

set_option linter.unusedSectionVars false


theorem u4InnRest_holds : U4InnRest :=
  u4InnRest_of_rows u4InnAt_d4two u4InnAt_sp8two

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
