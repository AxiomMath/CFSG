module

public import CFSG.RankThree.PartTwo.NotationBlocks

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open Matrix

section Models

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def IsOmegaPlusModel (T : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)) (m : ℕ) :
    Prop :=
  ∃ φ : W ≃ₗ[ZMod 2] (Fin m ⊕ Fin m → ZMod 2),
    (∀ g ∈ T, ∃ A ∈ omegaPlusTwo m,
      ∀ w : W, (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2)) *ᵥ φ w =
        φ ((g : W →ₗ[ZMod 2] W) w)) ∧
    ∀ A ∈ omegaPlusTwo m, ∃ g ∈ T,
      ∀ w : W, (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2)) *ᵥ φ w =
        φ ((g : W →ₗ[ZMod 2] W) w)

@[expose] def IsOmegaMinusModel (T : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)) (m : ℕ) :
    Prop :=
  ∃ φ : W ≃ₗ[ZMod 2] (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2),
    (∀ g ∈ T, ∃ A ∈ omegaMinusTwo m,
      ∀ w : W, (A : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ φ w =
        φ ((g : W →ₗ[ZMod 2] W) w)) ∧
    ∀ A ∈ omegaMinusTwo m, ∃ g ∈ T,
      ∀ w : W, (A : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ φ w =
        φ ((g : W →ₗ[ZMod 2] W) w)

@[expose] def IsAltModel (T : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)) (m : ℕ) :
    Prop :=
  ∃ (φ : W ≃+ altHeart m) (θ : T ≃* alternatingGroup (Fin m)),
    ∀ (g : T) (w : W) (x : evenWeight m), φ w = (x : altHeart m) →
      φ (((g : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) w) =
        (evenWeightPerm (θ g : Equiv.Perm (Fin m)) x : altHeart m)

end Models

end CFSG.HardMathSupport.Cooperstein.StructureLie
