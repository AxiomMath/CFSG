module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.LieType.SeitzGeneration

variable {F : Type*} [Field F] {n : ℕ}

structure KronData (p : ℕ) (ζ c : F) (A B C : Matrix (Fin n) (Fin n) F) (u₀ : Fin n → F) :
    Prop where
  prime : p.Prime
  odd : p ≠ 2
  hpF : (p : F) ≠ 0
  prim : IsPrimitiveRoot ζ p
  notPow : ∀ b : F, b ^ p ≠ c
  hA : A ^ p = 1
  hB : B ^ p = 1
  hC : C ^ p = c • (1 : Matrix (Fin n) (Fin n) F)
  hAB : A * B = ζ • (B * A)
  hAC : A * C = C * A
  hBC : B * C = C * B
  hu : u₀ ≠ 0
  hBu : B.mulVec u₀ = u₀
  irr : ∀ W : Submodule F (Fin n → F), (∀ w ∈ W, A.mulVec w ∈ W) → (∀ w ∈ W, B.mulVec w ∈ W) →
    (∀ w ∈ W, C.mulVec w ∈ W) → W = ⊥ ∨ W = ⊤

end CFSG.LieType.SeitzGeneration
