module

public import CFSG.GH74.GLS.Stage12.Interface
public import CFSG.GH74.Uniqueness.SU.SU13Stmts

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.GLS

theorem isTwoAlt_of_isDoubleCoverOfAlt {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : IsDoubleCoverOfAlt X n) : K.IsTwoAlt X n :=
  ⟨h.1, inferInstance, h.2.1, h.2.2⟩

theorem s_noTwoAnNineTen_of_thm231 (h : Thm231Stmt) : Stage12.S_noTwoAnNineTen := by
  intro G _ _ hStd
  have key : ∀ n : ℕ, (n = 9 ∨ n = 10) → ¬ Stage12.OneClassDoubleCover G n := by
    rintro n hn ⟨z, ⟨hz, -⟩, -, hdc⟩
    exact h G hStd.kps.1 hStd.kps.2.1 z hz n hn (isTwoAlt_of_isDoubleCoverOfAlt hdc)
  exact ⟨key 9 (Or.inl rfl), key 10 (Or.inr rfl)⟩

end CFSG.GH74.Uniqueness.SU.SU13
