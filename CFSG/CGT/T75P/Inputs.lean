module

public import CFSG.CGT.Timmesfeld75.PaperSteps

public section

namespace CFSG.CGT.T75P

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.Assembly.LowTwoRank

@[expose] def Odd81 : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), StepHyp T T₁ →
    Nat.card T / Nat.card (normIn T T₁) = 2 ^ 1 → Nat.card T = (2 ^ 1) ^ 3 →
    NaturalSL T (hSub T (normIn T₁ T)) 3 1 →
    Odd (T.relIndex (Subgroup.centralizer (T : Set G)))

@[expose] def Odd82 : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), StepHyp T T₁ →
    Nat.card T / Nat.card (normIn T T₁) = 2 ^ 1 → Nat.card T = (2 ^ 1) ^ 4 →
    NaturalSL T (hSub T (normIn T₁ T)) 4 1 →
    Odd (T.relIndex (Subgroup.centralizer (T : Set G)))

@[expose] def A8SylowInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ T H : Subgroup G, T ≤ H → IsWC T → NaturalSL T H 3 1 →
      (∃ K : Subgroup G, K ≤ H ∧ T ⊓ K = ⊥ ∧ T ⊔ K = H) → Odd H.index →
        Nonempty (G ≃* alternatingGroup (Fin 8)) ∨ Nonempty (G ≃* alternatingGroup (Fin 9))

@[expose] def M24SylowInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ T H : Subgroup G, T ≤ H → IsWC T → NaturalSL T H 4 1 → Odd H.index →
      StatedClassicalModel G .PSL 5 2 1 ∨ CFSG.Blueprint.NativeSporadic.IsSporadic G .M24

end CFSG.CGT.T75P
