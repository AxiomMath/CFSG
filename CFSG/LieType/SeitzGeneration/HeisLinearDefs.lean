module

public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix

@[expose] def heisShiftMat (F : Type*) [Field F] (p : ℕ) : Matrix (Fin p) (Fin p) F :=
  (finRotate p).permMatrix F

@[expose] def heisDiagMat {F : Type*} [Field F] {p : ℕ} (ω : F) : Matrix (Fin p) (Fin p) F :=
  Matrix.diagonal fun i => ω ^ (i : ℕ)

@[expose] def heisFourierMat {F : Type*} [Field F] {p : ℕ} (ζ : F) : Matrix (Fin p) (Fin p) F :=
  Matrix.of fun i j => ζ ^ ((i : ℕ) * (j : ℕ))

@[expose] def TorusFourierGen (F : Type*) [Field F] (p : ℕ) : Prop :=
  ∀ ζ : F, IsPrimitiveRoot ζ p → ∀ K : Subgroup (SpecialLinearGroup (Fin p) F),
    (∀ g : SpecialLinearGroup (Fin p) F,
      (∃ t : Fin p → F, (g : Matrix (Fin p) (Fin p) F) = Matrix.diagonal t) → g ∈ K) →
    (∀ g : SpecialLinearGroup (Fin p) F,
      (∃ t : Fin p → F, (g : Matrix (Fin p) (Fin p) F) * heisFourierMat ζ =
        heisFourierMat ζ * Matrix.diagonal t) → g ∈ K) → K = ⊤

end CFSG.LieType.SeitzGeneration
