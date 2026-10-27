module

public import CFSG.CGT.Timmesfeld75.StrongClosure
public import CFSG.Timmesfeld.Defs

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open CFSG.Assembly.LowTwoRank

@[expose] def Lemma26Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsWC T → 2 < Nat.card T →
    (∃ d₀ : G, classD T = {g | IsConj d₀ g}) →
    CFSG.Timmesfeld.IsRootInvolutionSet (classD T) → Subgroup.closure (classD T) = ⊤ →
      ((∃ n m : ℕ, 2 ≤ n ∧ 1 ≤ m ∧ StatedClassicalModel (G ⧸ Subgroup.center G) .PSL n 2 m) ∨
        (∃ m : ℕ, 2 ≤ m ∧ StatedClassicalModel (G ⧸ Subgroup.center G) .PSU 3 2 m) ∨
        (∃ s : ℕ, Odd s ∧ 3 ≤ s ∧
          CFSG.Blueprint.LieModel (G ⧸ Subgroup.center G) .twistedB2 0 2 s) ∨
        Nonempty (G ⧸ Subgroup.center G ≃* alternatingGroup (Fin 6))) ∧
      (¬ Nonempty (G ⧸ Subgroup.center G ≃* alternatingGroup (Fin 6)) →
        ∀ U₁ U₂ V₁ V₂ : Subgroup G, (∃ x : G, U₁ = conjSubgroup x T) →
          (∃ x : G, U₂ = conjSubgroup x T) → (∃ x : G, V₁ = conjSubgroup x T) →
          (∃ x : G, V₂ = conjSubgroup x T) → U₁ ≠ U₂ → V₁ ≠ V₂ →
            ∃ g : G, conjSubgroup g U₁ = V₁ ∧ conjSubgroup g U₂ = V₂)

end CFSG.CGT.Timmesfeld75
