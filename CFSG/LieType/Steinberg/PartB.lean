module

public import CFSG.LieType.Steinberg.Extras
public import CFSG.LieType.Steinberg.OfCartan
public import CFSG.LieType.Steinberg.Statement
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.LieType.Steinberg

open CFSG.LieType.Universal CFSG.LieType.CurtisTits
open scoped commutatorElement

variable {K : Type*} [Group K]

@[expose] def sl2Upper {k : Type*} [Field k] (c : k) : Matrix.SpecialLinearGroup (Fin 2) k :=
  ⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def sl2Lower {k : Type*} [Field k] (c : k) : Matrix.SpecialLinearGroup (Fin 2) k :=
  ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def weylElement {k : Type*} [Field k] {r : ℕ} (x : (Fin r → ℤ) → k → K) (i : Fin r)
    (t : kˣ) : K :=
  x (Pi.single i 1) t * x (-Pi.single i 1) (-(t⁻¹ : kˣ)) * x (Pi.single i 1) t

structure ChevalleyExtras (D : UniversalRootDatum K) (k : Type*) [Field k]
    (x : (Fin D.rank → ℤ) → k → K) (C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ)
    (O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)) : Prop where
  param : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible)
    D.rootGroup x
  comm : CommutatorFormula x O C
  weyl : ∀ i, ∀ β ∈ D.roots, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (t : kˣ) (u : k),
    weylElement x i t * x β u * (weylElement x i t)⁻¹ =
      x (CFSG.LieType.RootSystem.reflection D.cartan i β)
        ((ε : k) * ((t ^ (-(∑ j, D.cartan i j * β j)) : kˣ) : k) * u)
  rankOne : ∀ i, ∃ φ : Matrix.SpecialLinearGroup (Fin 2) k →* K, Function.Injective φ ∧
    (∀ c, φ (sl2Upper c) = x (Pi.single i 1) c) ∧ ∀ c, φ (sl2Lower c) = x (-Pi.single i 1) c
  prodInjective : ∀ (f : (Fin D.rank → ℤ) →+ ℤ) (L : List (Fin D.rank → ℤ)), L.Nodup →
    (∀ γ ∈ L, γ ∈ D.roots ∧ 0 < f γ) → L.Pairwise (fun γ δ => f γ ≤ f δ) →
      ProdInjectiveFor D.rootGroup L
  rankTwo : ∀ i, ∃ δ ∈ D.roots, ∃ γ ∈ D.roots, δ + γ ≠ 0 ∧ ∃ j : ℕ, (j = 1 ∨ j = 2) ∧
    Pi.single i 1 = δ + j • γ ∧ IsUnit (C δ γ (1, j) : k)

end CFSG.LieType.Steinberg
