module

public import CFSG.CGT.PushingUpLit.A78Sp4.Cut
public import CFSG.CGT.PushingUpLit.A78Sp4.Final
public import CFSG.CGT.PushingUpLit.A78Sp4.StrongClosure

public section

namespace CFSG.CGT.PushingUpLit.A78Sp4

@[expose] def Sp4Chain410GE3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L L₂ V V₂ Z Z₂ J T S M M₂ : Subgroup G) (e : ℕ),
    Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e → 3 ≤ e → Sp4Stmt410 V V₂ Z Z₂ J

@[expose] def Sp4Chain410Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L L₂ V V₂ Z Z₂ J T S M M₂ : Subgroup G) (e : ℕ),
    Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e → e = 2 → Sp4Stmt410 V V₂ Z Z₂ J

theorem sp4ChainGE3_of_410 (h : Sp4Chain410GE3) : Sp4ChainGE3 := by
  intro G _ _ L L₂ V V₂ Z Z₂ J T S M M₂ e hloc he
  have h410 := h G L L₂ V V₂ Z Z₂ J T S M M₂ e hloc he
  exact sp4_final hloc h410 (sp4_M hloc h410)

theorem sp4ChainTwo_of_410 (h : Sp4Chain410Two) : Sp4ChainTwo := by
  intro G _ _ L L₂ V V₂ Z Z₂ J T S M M₂ e hloc he
  have h410 := h G L L₂ V V₂ Z Z₂ J T S M M₂ e hloc he
  exact sp4_final hloc h410 (sp4_M hloc h410)

end CFSG.CGT.PushingUpLit.A78Sp4
