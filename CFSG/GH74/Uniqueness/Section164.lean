module

public import CFSG.GH74.Uniqueness.Section164C

public section

namespace CFSG.GH74.Uniqueness

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.lemma164
    (S : ZDSetup X Z M) (h121 : Thm121Stmt Z M) (h161 : Lemma161Stmt Z M)
    (h162 : Lemma162Stmt Z M) (h163 : Lemma163Stmt Z M) : Lemma164Stmt Z M := by
  intro c n i e hB
  exact ⟨S.lemma164a h121 h161 h162 c, S.lemma164b h121 h161 h162 c hB,
    fun hS hconj => S.lemma164c h162 h163 c hB hS hconj⟩

end CFSG.GH74.Uniqueness
