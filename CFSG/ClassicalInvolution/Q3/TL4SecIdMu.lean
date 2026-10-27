module

public import CFSG.ClassicalInvolution.Q3.TL4ModelFacts

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.Blueprint

section Shapes

variable {X : Type} [Group X]

@[expose] def SecIdQ8Shape (c : CompData) (Φ : Set (Subgroup X)) : Prop :=
  ∃ ψ : c.G →* X, Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center c.G ∧
    ∀ L ∈ Φ, ∃ R ∈ c.fund, IsSylow2In L (R.map ψ)

@[expose] def SecIdExitS3 (Φ : Set (Subgroup X)) : Prop :=
  Disconnected.DEdgeless Φ ∧ (∃ L ∈ Φ, (omegaStarNbr Φ L).Nonempty) ∧
    ∃ (R : Subgroup X) (S : Sylow 2 R) (z : X), EdgelessMember3 R S z ∧
      CoreAssembly.conjClass (tightCore R) = Φ ∧ ¬ TightInO2 z ∧
      ((¬ TightActs3 R z ∧ (Thm6Exit X ∨ TightTwisted X z)) ∨
        Nonempty (X ⧸ Subgroup.center X ≃* NativeSporadic.Carrier .M12))

@[expose] def SecIdE8 (Φ : Set (Subgroup X)) : Prop :=
  (∃ E : Subgroup X, TC.Thin.E8Struct ⊤ E) ∧ T3.DStarConnected Φ

@[expose] def SecIdE64 (Φ : Set (Subgroup X)) : Prop :=
  Nonempty (TC.Thin.AEIdentOn Φ 7 AE.e64Sets AE.e64Sub) ∧ T3.DStarConnected Φ

@[expose] def SecIdSp6 (Φ : Set (Subgroup X)) : Prop :=
  Subgroup.center X ≠ ⊥ ∧ LieModel (X ⧸ Subgroup.center X) .PSp 3 2 1 ∧ T3.DStarConnected Φ

@[expose] def SecIdWNormal (Φ : Set (Subgroup X)) : Prop :=
  (∃ V : Subgroup X, WSet Φ = {V}) ∧
    (∀ A ∈ Φ, ∀ B ∈ omegaNbr Φ A, ∀ C ∈ omegaNbr Φ A, C ∉ omegaNbr Φ B) ∧ T3.DStarConnected Φ

end Shapes

section Cit3


variable {X : Type} [Group X]

@[expose] def SecIdLieS3 (Φ : Set (Subgroup X)) : Prop :=
  SecIdQ8Shape (CompData.model .PSU 3) Φ ∨ SecIdQ8Shape (CompData.model .G2 0) Φ ∨
    SecIdQ8Shape (CompData.model .trialityD4 0) Φ

@[expose] def SecIdLieS4 (Φ : Set (Subgroup X)) : Prop :=
  SecIdQ8Shape (CompData.model .PSU 4) Φ ∨ SecIdQ8Shape (CompData.model .POmegaOdd 3) Φ ∨
    SecIdQ8Shape (CompData.model .POmegaMinus 4) Φ

@[expose] def SecIdMuS3S4Id (Φ : Set (Subgroup X)) : Prop :=
  ¬ Disconnected.DConnected Φ ∧
    (SecIdLieS3 Φ ∨ SecIdLieS4 Φ ∨ SecIdExitS3 Φ ∨ SecIdE8 Φ ∨ SecIdE64 Φ ∨ SecIdSp6 Φ ∨
      SecIdWNormal Φ)

@[expose] def SecIdStarNbrId3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)), TypeRFam 3 Φ →
    classicalInvolutionOddCore X = ⊥ → omegaGen Φ = ⊤ →
    (∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L') → SecIdMuS3S4Id Φ →
      ∀ L ∈ Φ, ∃ L' ∈ Φ, L' ∈ omegaStarNbr Φ L ∧ L' ∉ omegaNbr Φ L

@[expose] def SecIdStarOrbId3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)), TypeRFam 3 Φ →
    classicalInvolutionOddCore X = ⊥ → omegaGen Φ = ⊤ →
    (∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L') → SecIdMuS3S4Id Φ →
      ∀ L ∈ Φ, ∀ L' ∈ omegaStarNbr Φ L, L' ∉ omegaNbr Φ L → ∀ a b : X,
        IsUniqueInvolution L a → IsUniqueInvolution L' b →
          ∃ g : X, g * a * g⁻¹ = b ∧ g * b * g⁻¹ = a * b

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
