module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdMu

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77

section Defs

@[expose] def LieKindNamed (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m : ℕ) : Prop :=
  (t = .PSL ∧ m = 3) ∨ (t = .PSU ∧ m = 3) ∨ (t = .PSp ∧ m = 2) ∨ (t = .PSL ∧ m = 4) ∨
    (t = .PSU ∧ m = 4) ∨ (t = .POmegaOdd ∧ m = 3) ∨ (t = .POmegaMinus ∧ m = 4) ∨
    (t = .G2 ∧ m = 0) ∨ (t = .trialityD4 ∧ m = 0)

variable {X : Type} [Group X]

@[expose] def LieLinkSection (Φ : Set (Subgroup X)) : Prop :=
  TypeRFam 3 Φ ∧ classicalInvolutionOddCore X = ⊥ ∧ omegaGen Φ = ⊤ ∧
    ∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L'

end Defs

section Cit3


@[expose] def LieKindTwoNbrs : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X))
    (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m : ℕ), IsFundTag t →
    CFSG.Assembly.LowTwoRank.StatedLieAdmissible t m 3 1 → ¬ LieKindNamed t m →
    LieLinkSection Φ → SecIdQ8Shape (CompData.model t m) Φ →
      ∃ L ∈ Φ, ∃ M ∈ omegaNbr Φ L, ∃ M' ∈ omegaNbr Φ L, M ≠ M'

@[expose] def LieKindE4Edge : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)) (c : CompData),
    (c = CompData.model .PSp 2 ∨ c = CompData.model .PSL 4) → LieLinkSection Φ →
      SecIdQ8Shape c Φ → ∃ L ∈ Φ, (omegaNbr Φ L).Nonempty

@[expose] def LieKindE4Cover : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (c : CompData),
    (c = CompData.model .PSp 2 ∨ c = CompData.model .PSL 4) → ∀ ψ : c.G →* Q,
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center c.G →
        ∀ x ∈ Subgroup.center Q, ∃ f ∈ Subgroup.center c.G, ψ f = x

@[expose] def LieKindZ2NoStar : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)) (c : CompData),
    (c = CompData.model .PSL 3 ∨ c = CompData.m11) → LieLinkSection Φ → SecIdQ8Shape c Φ →
      ∀ L ∈ Φ, omegaStarNbr Φ L = ∅

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
