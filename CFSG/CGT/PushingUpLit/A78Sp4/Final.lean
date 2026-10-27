module

public import CFSG.CGT.PushingUpLit.A78Sp4.Transfer
public import CFSG.CGT.PushingUpLit.A78Sp4.FieldInv

public section

namespace CFSG.CGT.PushingUpLit.A78Sp4

variable {G : Type} [Group G] [Finite G] {L L₂ V V₂ Z Z₂ J T S M M₂ : Subgroup G} {e : ℕ}

theorem sp4_final (h : Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e) (h410 : Sp4Stmt410 V V₂ Z Z₂ J)
    (hM : Sp4StmtM S J) : False := by
  have hTJ : T = J := sp4_412 h hM
  have hSJ : S = J := sp4_413 h h410 hM hTJ
  obtain ⟨s, hsS, hsT⟩ := h.base.exists_swap
  apply hsT
  rw [hTJ, ← hSJ]
  exact hsS

end CFSG.CGT.PushingUpLit.A78Sp4
