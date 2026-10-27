module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27Shape

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup

@[expose] def Seitz77CaseAFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A V₁ V₂ W X O Sy Wt P : Subgroup G), Hyp G A →
    ∀ d : Datum A, Radicals d.V V₁ V₂ → (W = V₁ ∨ W = V₂) →
    ∀ H : Setup27 A W X O Sy Wt P d.t, (∃ w : WData d W, w.S = Sy ∧ w.W = Sy ⊓ Wt) →
      Out27A (Ntil27 (Sy ⊓ Wt)) H.X27 H.ttilde27 → False

@[expose] def Seitz77CaseBFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A V₁ V₂ : Subgroup G), Hyp G A → ∀ d : Datum A,
    Radicals d.V V₁ V₂ →
    (∀ W : Subgroup G, W = V₁ ∨ W = V₂ → ∃ (X O Sy Wt P : Subgroup G)
      (H : Setup27 A W X O Sy Wt P d.t), (∃ w : WData d W, w.S = Sy ∧ w.W = Sy ⊓ Wt) ∧
        Out27B (Ntil27 (Sy ⊓ Wt)) H.X27 H.ttilde27) → False

end CFSG.OddStandard.Seitz77
