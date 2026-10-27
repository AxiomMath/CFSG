module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGField
public import CFSG.Open.FusionDefs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

@[expose] def IsTwoQuasisimple (K : Type*) [Group K] : Prop :=
  Group.IsPerfect K ∧ IsQuasisimple (K ⧸ pPrimeCore 2 K)

@[expose] def IsOfType (F : (Y : Type) → [Group Y] → Prop) (K : Type*) [Group K] : Prop :=
  IsTwoQuasisimple K ∧ ∃ (Y : Type) (_ : Group Y), F Y ∧ Nonempty (K ⧸ Open.fusionZStar K ≃* Y)

@[expose] def IsBlowup (X : Type) [Group X] (Y : Type) [Group Y] : Prop :=
  Finite X ∧ IsSimpleGroup X ∧ ∃ α : MulAut X, orderOf α = 2 ∧
    ∃ L : Subgroup ↥(fixedPoints α), IsPComponent 2 L ∧
      Nonempty (↥L ⧸ Open.fusionZStar ↥L ≃* Y)

inductive InClosure (F : (Y : Type) → [Group Y] → Prop) : (X : Type) → [Group X] → Prop
  | base {Y : Type} [Group Y] : F Y → InClosure F Y
  | blowup {X Y : Type} [Group X] [Group Y] : InClosure F Y → Blueprint.Catalog X →
      IsBlowup X Y → InClosure F X

@[expose] def HarrisF (p : ℕ) : (Y : Type) → [Group Y] → Prop :=
  fun Y _ => InClosure
    (fun (Y' : Type) [Group Y'] => ∃ n : ℕ, (if p = 3 then 2 else 1) ≤ n ∧
      Blueprint.LieModel Y' .PSL 2 p n) Y

end CFSG.ComponentClassification.HarrisLit
