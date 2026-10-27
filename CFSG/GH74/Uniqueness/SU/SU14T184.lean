module

public import CFSG.GH74.Uniqueness.SU.SU7Stmts

public section

namespace CFSG.GH74.Uniqueness.SU.SU14

theorem thm184_of_stmts (h186 : SU4.Lemma186Stmt) (h18H : SU4.Lemma18HStmt)
    (h189 : SU4.Prop189Stmt) (hfalse : SU7.Sec19FalseStmt) : SU7.Thm184Stmt := by
  intro G _ _ S U M hHyp
  have hno : SU4.Concl184b M := by
    intro V hV
    obtain ⟨V', x, z, hconf⟩ := h18H G S U M hHyp ⟨V, hV⟩
    exact hfalse G S U M V' x z hconf hHyp (h189 G S U M V' x z hconf hHyp)
  exact ⟨h186 G S U M hHyp hno, hno⟩

end CFSG.GH74.Uniqueness.SU.SU14
