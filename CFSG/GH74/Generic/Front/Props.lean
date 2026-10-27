module

public import CFSG.GH74.Generic.Front.Defs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.GH74.L5U5.Models

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def ShapeModel (K : Type) [Group K] : Prop :=
  IsSL4Model K ∨ ∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧
    Nonempty (K ≃* StatedSp 2 F)

@[expose] def FrontData0Statement : Prop :=
  ∀ (K : Type) [Group K], ShapeModel K → Nonempty (FrontData0 K)

@[expose] def NoCentralStatement : Prop :=
  ∀ (K : Type) [Group K], ShapeModel K → NoCentral K

@[expose] def FrontDataStatement : Prop :=
  ∀ (K : Type) [Group K], ShapeModel K → Nonempty (FrontData K)

theorem frontDataStatement_of (h0 : FrontData0Statement) (hc : NoCentralStatement) :
    FrontDataStatement := fun K _ hK => by
  obtain ⟨D⟩ := h0 K hK
  exact ⟨⟨D, hc K hK⟩⟩

@[expose] def OuterSolvableStatement : Prop :=
  ∀ (K : Type) [Group K], ShapeModel K → Group.IsSolvable (Outer K)

@[expose] def OuterThreeStatement : Prop :=
  ∀ (K : Type) [Group K], ShapeModel K → ThreeModel K → ∀ o : Outer K, Odd (orderOf o) → o = 1

@[expose] def OuterStatement : Prop :=
  OuterSolvableStatement ∧ OuterThreeStatement

@[expose] def SpOuterInvolution : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Odd (Nat.card F) →
    ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X) [K.Normal], Nonempty (↥K ≃* StatedSp 2 F) →
      Subgroup.centralizer (K : Set X) ≤ K → Gen4 X →
        ∀ v : X, v * v = 1 → v ∉ K →
          ∃ H : Subgroup X, H ≤ K ⊓ Subgroup.centralizer ({v} : Set X) ∧
            (∀ z ∈ Subgroup.center ↥K, (z : X) ∈ H) ∧ GoodSub (ThreeModel ↥K) H

end CFSG.GH74.Generic
