module

public import CFSG.CGT.PushingUpLit.CGT6.EmbNatBase
public import CFSG.CGT.PushingUpLit.CGT6.Embedding
public import CFSG.CGT.PushingUpLit.CGT6.Props

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUp
open scoped commutatorElement

@[expose] def NatLiftStatement : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X Y : Subgroup (MulAut V)) (a b : ℕ), 2 ≤ a → 1 ≤ b → b ≤ a →
      ∀ θ : X ≃* alternatingGroup (Fin (2 * a + 1)),
        IsNatSectionWith (altAct (2 * a + 1)) θ (commV X) ⊥ →
        ∀ F : Finset (Fin (2 * a + 1)), F.card = (2 * a + 1) - (2 * b + 1) → Y ≤ X →
          (Y.subgroupOf X).map θ.toMonoidHom = altStabilizer (2 * a + 1) F →
          InClassX ↥(yuHol X) ∧ ArrowNat (yuHol Y) (yuHol X)

@[expose] def NatRecogStatement : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X : Subgroup (MulAut V)) (a : ℕ), 2 ≤ a →
      ∀ θ : X ≃* alternatingGroup (Fin (2 * a + 1)),
        (∀ w : V, (∀ x : X, (x : MulAut V) w = w) → w = 1) →
        ∀ (i₀ : Fin (2 * a + 1)) (v : V), v ≠ 1 →
          (∀ x : X, θ x ∈ altStabilizer (2 * a + 1) {i₀} → (x : MulAut V) v = v) →
          IsNatSectionWith (altAct (2 * a + 1)) θ (orbitSpan X v) ⊥

end CFSG.CGT.PushingUpLit.CGT6
