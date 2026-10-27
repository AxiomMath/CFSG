module

public import CFSG.LieType.SeitzGeneration.UnitaryCenters

public section

namespace CFSG.LieType.SeitzGeneration.HeisP

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.SeitzGeneration.Centers

variable {K : Type} [Field K] {p : ℕ}

@[expose] def Zm (ζ : K) : Matrix (Fin p) (Fin p) K := Matrix.diagonal fun a => ζ ^ (a : ℕ)

@[expose] def Gj [NeZero p] (ζ α : K) (j : ℕ) : Matrix (Fin p) (Fin p) K :=
  Matrix.of fun a b =>
    if a = b + 1 then ζ ^ (j * (b : ℕ)) * (if (b : ℕ) + 1 = p then α else 1) else 0

structure HeisFrameP (σ : K ≃+* K) (p n m : ℕ) [NeZero p] (X Y : Matrix (Fin n) (Fin n) K)
    (α ζ : K) where
  f : Fin p → Fin m → Fin n → K
  on : ∀ k r l s, herm σ (f k r) (f l s) = if k = l ∧ r = s then 1 else 0
  span : ∀ v : Fin n → K, ∃ c : Fin p → Fin m → K, v = ∑ k, ∑ r, c k r • f k r
  hY : ∀ k r, Y *ᵥ f k r = ζ ^ (k : ℕ) • f k r
  hX : ∀ k r, X *ᵥ f k r = (if (k : ℕ) + 1 = p then α else 1) • f (k + 1) r

end CFSG.LieType.SeitzGeneration.HeisP
