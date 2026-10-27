module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFormSimilitude
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourNonsplitAction
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorSplitFour

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

section Data

variable {k : Type} [Field k] {m : ℕ} (δ : kˣ)

@[expose] def rowOAction :
    SpecialLinearGroup (Fin 2) (extension (δ : k)) →*
      (hermitianSubmodule (δ : k) ≃ₗ[k] hermitianSubmodule (δ : k)) where
  toFun g := hermitianCongruence (δ : k) (SpecialLinearGroup.toGL g)
  map_one' := by rw [map_one, hermitianCongruence_one]
  map_mul' g h := by rw [map_mul, hermitianCongruence_mul]

theorem rowOAction_val (g : SpecialLinearGroup (Fin 2) (extension (δ : k)))
    (X : hermitianSubmodule (δ : k)) :
    (rowOAction δ g X).val = (g : Matrix (Fin 2) (Fin 2) (extension (δ : k))) * X.val *
      (g : Matrix (Fin 2) (Fin 2) (extension (δ : k))).conjTranspose := rfl

@[expose] def rowOHom (ψ : (Fin m → k) ≃ₗ[k] hermitianSubmodule (δ : k)) :
    SpecialLinearGroup (Fin 2) (extension (δ : k)) →* GL (Fin m) k :=
  (linearConjGL ψ).comp (rowOAction δ)

@[expose] def rowOJ (ψ : (Fin m → k) ≃ₗ[k] hermitianSubmodule (δ : k)) :
    Subgroup (MulAut (projectiveSL m k)) :=
  ((conjAut m k).comp (rowOHom δ ψ)).range

@[expose] def rowOFixed (R : GL (Fin m) k) : Subgroup (GL (Fin m) k) :=
  CatalogueBGraphForm.similitudeGroup m k R ⊓
    ((powMonoidHom 4 : kˣ →* kˣ).range).comap GeneralLinearGroup.det

end Data

@[expose] def SelectorRowO {A : Type} [Group A] (m : ℕ) (k : Type) [Field k]
    (ρ : A →* MulAut (projectiveSL m k)) (W : Subgroup A) (a : A) (L : Subgroup A) : Prop :=
  ∃ (δ : kˣ) (_ : ¬ IsSquare (δ : k)) (ψ : (Fin m → k) ≃ₗ[k] hermitianSubmodule (δ : k))
    (R C : GL (Fin m) k),
    (R : Matrix (Fin m) (Fin m) k)ᵀ = R ∧
    (∀ v : Fin m → k, v ⬝ᵥ ((R : Matrix (Fin m) (Fin m) k) *ᵥ v) =
      hermitianForm (δ : k) (ψ v)) ∧
    ρ a = conjAut m k C * (conjAut m k R⁻¹ * dualAut m k) * (conjAut m k C)⁻¹ ∧
    OuterAutomorphisms.inner (projectiveSL m k) ⊓ centralizer {ρ a} =
      ((rowOFixed R).map (conjAut m k)).map (MulAut.conj (conjAut m k C)).toMonoidHom ∧
    (∀ X : Subgroup (MulAut (projectiveSL m k)),
      CFSG.Assembly.IsComponentOf X
          (OuterAutomorphisms.inner (projectiveSL m k) ⊓ centralizer {ρ a}) ↔
        X = (rowOJ δ ψ).map (MulAut.conj (conjAut m k C)).toMonoidHom) ∧
    L.map ρ = (rowOJ δ ψ).map (MulAut.conj (conjAut m k C)).toMonoidHom ∧
    (rowOHom δ ψ).range ≤ CatalogueBGraphForm.isometryGroup m k R ∧
    (∀ g : SpecialLinearGroup (Fin 2) (extension (δ : k)),
      conjAut m k (rowOHom δ ψ g) = 1 ↔ g = 1 ∨ g = -1) ∧
    centralizer {ρ a} = (centralizer {conjAut m k R⁻¹ * dualAut m k}).map
      (MulAut.conj (conjAut m k C)).toMonoidHom ∧
    (centralizer {conjAut m k R⁻¹ * dualAut m k} : Set (MulAut (projectiveSL m k))) =
      {β | ∃ (B : GL (Fin m) k) (τ : k ≃+* k) (ε : ℕ), ε ≤ 1 ∧
        ((ε = 0 ∧ ∃ c : kˣ, (B : Matrix (Fin m) (Fin m) k)ᵀ * R * B = (c : k) •
            ((GeneralLinearGroup.map (τ : k →+* k) R : GL (Fin m) k) :
              Matrix (Fin m) (Fin m) k)) ∨
          (ε = 1 ∧ ∃ c : kˣ, (B : Matrix (Fin m) (Fin m) k)ᵀ * R * B = (c : k) •
            (((GeneralLinearGroup.map (τ : k →+* k) R)⁻¹ : GL (Fin m) k) :
              Matrix (Fin m) (Fin m) k))) ∧
        β = conjAut m k B * fieldAut m k τ * dualAut m k ^ ε} ∧
    (centralizer {a}).map ρ = ρ.range ⊓ (centralizer {conjAut m k R⁻¹ * dualAut m k}).map
      (MulAut.conj (conjAut m k C)).toMonoidHom ∧
    (W ⊓ centralizer {a}).map ρ = OuterAutomorphisms.inner (projectiveSL m k) ⊓
      (centralizer {conjAut m k R⁻¹ * dualAut m k}).map (MulAut.conj (conjAut m k C)).toMonoidHom

end CFSG.ComponentClassification.OddSelector
