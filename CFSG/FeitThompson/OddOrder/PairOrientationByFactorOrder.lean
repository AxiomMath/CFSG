module

public import CFSG.FeitThompson.OddOrder.PairedMaximalSubgroupsSwap
import CFSG.FeitThompson.OddOrder.CyclicDirectProductCoprimeFactors

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] [Finite G] {S T W₁ W₂ : Subgroup G}

namespace IsTypePPair

theorem coprime_natCard (h : IsTypePPair S T W₁ W₂) :
    (Nat.card W₁).Coprime (Nat.card W₂) := by
  have : IsCyclic (W₁ ⊔ W₂ : Subgroup G) := h.isCyclic_sup
  have hinf : W₁.subgroupOf (W₁ ⊔ W₂) ⊓ W₂.subgroupOf (W₁ ⊔ W₂) = ⊥ := by
    rw [Subgroup.subgroupOf, Subgroup.subgroupOf, ← Subgroup.comap_inf, h.inf_W₁_W₂]
    simp
  have hco := coprime_natCard_of_inf_eq_bot hinf
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : W₁ ≤ W₁ ⊔ W₂)).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : W₂ ≤ W₁ ⊔ W₂)).toEquiv] at hco

theorem natCard_ne (h : IsTypePPair S T W₁ W₂) : Nat.card W₁ ≠ Nat.card W₂ := fun he =>
  h.ne_bot_left (Subgroup.card_eq_one.mp (by simpa [Nat.Coprime, ← he] using h.coprime_natCard))

theorem isTypePPair_and_natCard_lt_or_swap (h : IsTypePPair S T W₁ W₂) :
    (IsTypePPair S T W₁ W₂ ∧ Nat.card W₁ < Nat.card W₂) ∨
      (IsTypePPair T S W₂ W₁ ∧ Nat.card W₂ < Nat.card W₁) :=
  (lt_or_gt_of_ne h.natCard_ne).imp (fun hlt => ⟨h, hlt⟩) fun hlt => ⟨h.symm, hlt⟩

theorem wlog_natCard_lt {P : Subgroup G → Subgroup G → Subgroup G → Subgroup G → Prop}
    (h : IsTypePPair S T W₁ W₂)
    (hswap : ∀ A B C D : Subgroup G, P B A D C → P A B C D)
    (hP : ∀ A B C D : Subgroup G, IsTypePPair A B C D → Nat.card C < Nat.card D → P A B C D) :
    P S T W₁ W₂ :=
  match h.isTypePPair_and_natCard_lt_or_swap with
  | .inl ⟨h', hlt⟩ => hP S T W₁ W₂ h' hlt
  | .inr ⟨h', hlt⟩ => hswap S T W₁ W₂ (hP T S W₂ W₁ h' hlt)

end IsTypePPair

end

end CFSG.FeitThompson
