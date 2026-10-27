module

public import CFSG.GH74.Uniqueness.Section174Quot

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.lemma174
    (S : ZDSetup X Z M) (h311 : Lemma311BenderStmt)
    (h166 : Cor166Stmt Z M) (h172 : Lemma172Stmt Z M) : Lemma174Stmt Z M := by
  intro c n e hB
  obtain ⟨A, s, hAB, hAodd, hsB, hs2, hs1, hsA, -, hc1, hc2, hpts, hN⟩ :=
    S.exists_pair_B0 h166 h172 c hB
  exact hB.false_of_pair S h311 hAB hAodd hsB hs2 hs1 hsA hpts hN hc1 hc2

end CFSG.GH74.Uniqueness
