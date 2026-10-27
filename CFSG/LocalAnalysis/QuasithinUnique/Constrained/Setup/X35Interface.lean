module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.Actor
public import CFSG.LocalAnalysis.QuasithinUnique.BenderInterfaces
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X35Basic

public section

namespace CFSG.QuasithinUnique.Setup.X35

open CFSG.Quasithin

structure ActorBase (V : Type) [CommGroup V] [Finite V] (H T M E : Subgroup (MulAut V)) :
    Prop where
  elementary : ∀ v : V, v * v = 1
  o2_trivial : ∀ N : Subgroup (MulAut V), N ≤ H → (N.subgroupOf H).Normal → IsPGroup 2 N → N = ⊥
  sylow : IsSylowTwoOf T H
  not_normal : ¬ (T.subgroupOf H).Normal
  max : T ≤ M ∧ M < H ∧ ∀ X : Subgroup (MulAut V), T ≤ X → X < H → X ≤ M
  offender : E ≤ H ∧ E ≠ ⊥ ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧
    Nat.card V ≤ Nat.card E * Nat.card (fixV E)

theorem ActorBase.of_ffActor {V : Type} [CommGroup V] [Finite V] {H T M E : Subgroup (MulAut V)}
    (h : FFActor V H T M E) : ActorBase V H T M E :=
  ⟨h.elementary, h.o2_trivial, h.sylow, h.not_normal, h.max, h.offender⟩

@[expose] def ActorComponentTransfer : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H T M E : Subgroup (MulAut V)),
    ActorBase V H T M E → ¬ Group.IsSolvable H →
    ∀ L : Subgroup (MulAut V), IsComponentIn L H →
      IsSylowTwoOf (autOn T L) (autOn H L) ∧ ¬ ((autOn T L).subgroupOf (autOn H L)).Normal ∧
        ∃ P : Subgroup (MulAut L), X35.IsUniqueMaxOver (autOn T L) P (autOn H L)

end CFSG.QuasithinUnique.Setup.X35
