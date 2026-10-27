module

public import CFSG.ClassicalInvolution.Q3.TL4InductDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.Blueprint
open CFSG.ClassicalInvolution.Disconnected (DConnected)

@[expose] def SecIdE4LinkCent : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightDatum R S t → TightCls Y R S t → ¬ TightInO2 t → Subgroup.center Y ≠ ⊥ →
      (LieModel (Y ⧸ Subgroup.center Y) .PSp 3 2 1 ∨
        LieModel (Y ⧸ Subgroup.center Y) .POmegaPlus 4 2 1) →
      ∀ B ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ v : Y,
        IsUniqueInvolution B v → t * v ∈ Subgroup.center Y

section Cit3


@[expose] def SecIdE2LinkGen : Prop :=
  ∀ n, CIT3Below n → TightBelowRPlus 3 n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightCls Y R S t →
      TightInO2 t → ¬ DConnected (CoreAssembly.conjClass (tightCore R)) →
      ∀ B ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ v : Y,
        IsUniqueInvolution B v →
          Subgroup.centralizer ({t} : Set Y) ⊔ Subgroup.centralizer ({v} : Set Y) ⊔
            Subgroup.centralizer ({t * v} : Set Y) = ⊤

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
