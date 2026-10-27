module

public import CFSG.LargeExtraspecial.A2ModBasic
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LargeExtraspecial

open Module CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def S12ExcModuleInputN : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (τ : StatedLieTag),
    τ ∈ ({.F4, .E6, .twistedE6, .E7, .E8} : Finset StatedLieTag) → LieModel X τ 0 2 1 →
    ∀ D : Set X, A2Mod.RootClass X D →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
      (Q : QuadraticForm (ZMod 2) V) (ρ : X →* (V ≃ₗ[ZMod 2] V)), A2Mod.A2Action D Q ρ → False

@[expose] def S12PSLModuleInputN : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (m : ℕ), 4 ≤ m → LieModel X .PSL m 2 1 →
    ∀ D : Set X, A2Mod.RootClass X D →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
      (Q : QuadraticForm (ZMod 2) V) (ρ : X →* (V ≃ₗ[ZMod 2] V)), A2Mod.A2Action D Q ρ →
      (∀ W : Submodule (ZMod 2) V, (∀ x, ∀ w ∈ W, ρ x w ∈ W) → W = ⊥ ∨ W = ⊤) →
      finrank (ZMod 2) V < 10

@[expose] def S12SpModuleInputN : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (m : ℕ), 3 ≤ m → LieModel X .PSp m 2 1 →
    ∀ D : Set X, A2Mod.RootClass X D →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
      (Q : QuadraticForm (ZMod 2) V) (ρ : X →* (V ≃ₗ[ZMod 2] V)), A2Mod.A2Action D Q ρ →
      (∀ W : Submodule (ZMod 2) V, (∀ x, ∀ w ∈ W, ρ x w ∈ W) → W = ⊥ ∨ W = ⊤) →
      finrank (ZMod 2) V < 10

@[expose] def S12OmegaModuleInputN : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (m : ℕ), 4 ≤ m →
    (LieModel X .POmegaPlus m 2 1 ∨ LieModel X .POmegaMinus m 2 1) →
    ∀ D : Set X, A2Mod.RootClass X D →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
      (Q : QuadraticForm (ZMod 2) V) (ρ : X →* (V ≃ₗ[ZMod 2] V)), A2Mod.A2Action D Q ρ →
      (∀ W : Submodule (ZMod 2) V, (∀ x, ∀ w ∈ W, ρ x w ∈ W) → W = ⊥ ∨ W = ⊤) →
      finrank (ZMod 2) V < 10 ∨ finrank (ZMod 2) V = 2 * m

end CFSG.LargeExtraspecial
