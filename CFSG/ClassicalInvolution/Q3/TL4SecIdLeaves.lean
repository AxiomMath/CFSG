module

public import CFSG.ClassicalInvolution.Q3.TL3T10

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.Blueprint
open scoped commutatorElement

@[expose] def SecIdE4OddCent : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightDatum R S t → TightCls Y R S t → ¬ TightInO2 t → Subgroup.center Y ≠ ⊥ →
      (LieModel (Y ⧸ Subgroup.center Y) .PSp 3 2 1 ∨
        LieModel (Y ⧸ Subgroup.center Y) .POmegaPlus 4 2 1) →
      TightOddCent t

@[expose] def SecIdE4Edge : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightDatum R S t → TightCls Y R S t → ¬ TightInO2 t → Subgroup.center Y ≠ ⊥ →
      (LieModel (Y ⧸ Subgroup.center Y) .PSp 3 2 1 ∨
        LieModel (Y ⧸ Subgroup.center Y) .POmegaPlus 4 2 1) →
      ¬ TightEdgeless R

@[expose] def SecIdE4DStar : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightDatum R S t → TightCls Y R S t → ¬ TightInO2 t → Subgroup.center Y ≠ ⊥ →
      (LieModel (Y ⧸ Subgroup.center Y) .PSp 3 2 1 ∨
        LieModel (Y ⧸ Subgroup.center Y) .POmegaPlus 4 2 1) →
      T3.DStarConnected (CoreAssembly.conjClass (tightCore R))

@[expose] def SecIdE4NoClique5 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightDatum R S t → TightCls Y R S t → ¬ TightInO2 t → Subgroup.center Y ≠ ⊥ →
      (LieModel (Y ⧸ Subgroup.center Y) .PSp 3 2 1 ∨
        LieModel (Y ⧸ Subgroup.center Y) .POmegaPlus 4 2 1) →
      ∀ B : Fin 5 → Subgroup Y, (∀ i, B i ∈ CoreAssembly.conjClass (tightCore R)) →
        Function.Injective B →
          ¬ ∀ i j, i ≠ j → B j ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (B i)

@[expose] def SecIdE2Edgeless : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightDatum R S t → TightCls Y R S t → TightInO2 t → TightEdgeless R →
      (∃ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
        MuIsoZ2 (CoreAssembly.conjClass (tightCore R)) W) →
      tightCore R = ⊤

@[expose] def SecIdE2DStar : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightDatum R S t → TightCls Y R S t → TightInO2 t → ¬ TightEdgeless R →
      ¬ T3.DStarConnected (CoreAssembly.conjClass (tightCore R)) →
      Nonempty (TC.Thin.AEIdent (CoreAssembly.conjClass (tightCore R)) 5)

section Cit3


end Cit3

@[expose] def SecIdDStarOut3 {X : Type} [Group X] (Φ : Set (Subgroup X)) : Prop :=
  LieModel (X ⧸ Subgroup.center X) .PSp 2 3 1 ∨ LieModel (X ⧸ Subgroup.center X) .PSL 4 3 1 ∨
    Nonempty (TC.Thin.AEIdent Φ 5)

@[expose] def SecIdMuS3S4 (X : Type) [Group X] : Prop :=
  LieModel (X ⧸ Subgroup.center X) .PSU 3 3 1 ∨ LieModel (X ⧸ Subgroup.center X) .G2 0 3 1 ∨
    LieModel (X ⧸ Subgroup.center X) .trialityD4 0 3 1 ∨
    NativeSporadic.IsSporadic (X ⧸ Subgroup.center X) .M12 ∨
    LieModel (X ⧸ Subgroup.center X) .PSU 4 3 1 ∨
    LieModel (X ⧸ Subgroup.center X) .POmegaOdd 3 3 1 ∨
    LieModel (X ⧸ Subgroup.center X) .POmegaMinus 4 3 1

end CFSG.ClassicalInvolution.Q3.TL4
