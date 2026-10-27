module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

@[expose] def SchreierFor (C : CFSG.Assembly.GroupProp) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) → C X →
    Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)

@[expose] def KProperOrdinaryLocalBPumpUp (C : CFSG.Assembly.GroupProp) : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.Assembly.KProper C H →
    (∀ Q : Subgroup H, CFSG.Assembly.ComponentType.IsTwoPComponent Q →
      CFSG.Assembly.IsComponentOf Q ⊤) →
    ∀ t : H, orderOf t = 2 → ∀ J : Subgroup H,
      CFSG.Assembly.IsComponentOf J (centralizer ({t} : Set H)) →
      J ≤ CFSG.layer H ∧
      ∃ L : Subgroup H, CFSG.IsComponent L ∧
        ((conjSub t⁻¹ L = L ∧ CFSG.Assembly.IsComponentOf J (L ⊓ centralizer ({t} : Set H))) ∨
          (conjSub t⁻¹ L ≠ L ∧
            (J : Set H) = {g | ∃ x ∈ L, x * (t⁻¹ * x * t) = g} ∧
            (∃ δ : L →* J, (∀ x : L, (δ x : H) = x * (t⁻¹ * x * t)) ∧
              Function.Surjective δ ∧ δ.ker ≤ center L) ∧
            Nonempty (J ⧸ center J ≃* L ⧸ center L)))

end CFSG.LocalAnalysis.ComponentInitial
