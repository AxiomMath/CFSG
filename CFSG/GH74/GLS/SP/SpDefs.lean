module

public import CFSG.GH74.GLS.SP.Transfer
public import CFSG.LieType.Universal.SymplecticExtras
public import CFSG.LieType.Steinberg.Bruhat
public import CFSG.GH74.BNPair.Coordinatization

public noncomputable section

namespace CFSG.GH74.GLS.SP

open CFSG.GH74.BNPair CFSG.LieType.Universal.Symplectic CFSG.LieType.Steinberg
  CFSG.Assembly.LowTwoRank

section Data

variable (F : Type) [Field F]

@[expose] def spB : Subgroup (StatedSp 2 F) := borel (rootDatum 2 F) (torus 2 F)

@[expose] def spN : Subgroup (StatedSp 2 F) := weylN (weylRep 2 F) (torus 2 F)

@[expose] def spU : Subgroup (StatedSp 2 F) := posUnipotent (rootDatum 2 F)

@[expose] def spUneg : Subgroup (StatedSp 2 F) := negUnipotent (rootDatum 2 F)

@[expose] def spT : Subgroup (StatedSp 2 F) := ⨆ i, torus 2 F i

end Data

@[expose] def octRoot (i : ℤ) : Fin 2 → ℤ :=
  if i = 1 then ![1, 0] else if i = 2 then ![2, 1] else if i = 3 then ![1, 1]
  else if i = 4 then ![0, 1] else if i = -1 then ![-1, 0] else if i = -2 then ![-2, -1]
  else if i = -3 then ![-1, -1] else if i = -4 then ![0, -1] else 0

@[expose] def octGroup (F : Type) [Field F] (i : ℤ) : Subgroup (StatedSp 2 F) :=
  (rootDatum 2 F).rootGroup (octRoot i)

structure SpOctagon (F : Type) [Field F] : Prop where
  ne_bot : ∀ i : ℤ, IsRoot 4 i → octGroup F i ≠ ⊥
  invariant : ∀ i : ℤ, IsRoot 4 i → ∀ h ∈ spT F, ∀ x ∈ octGroup F i,
    h * x * h⁻¹ ∈ octGroup F i
  carrier_eq : ((spU F : Subgroup (StatedSp 2 F)) : Set (StatedSp 2 F)) =
    chainProd (octGroup F) (intList 1 ((4 : ℕ) : ℤ))
  unique : ∀ f g : ℤ → StatedSp 2 F,
    (∀ k ∈ intList 1 ((4 : ℕ) : ℤ), f k ∈ octGroup F k) →
    (∀ k ∈ intList 1 ((4 : ℕ) : ℤ), g k ∈ octGroup F k) →
    ((intList 1 ((4 : ℕ) : ℤ)).map f).prod = ((intList 1 ((4 : ℕ) : ℤ)).map g).prod →
      ∀ k ∈ intList 1 ((4 : ℕ) : ℤ), f k = g k
  reverse_eq : ∀ i j : ℤ, 1 ≤ i → i ≤ j → j ≤ ((4 : ℕ) : ℤ) →
    chainProd (octGroup F) (intList i j) = chainProd (octGroup F) (intList i j).reverse
  subgroup : ∀ i j : ℤ, 1 ≤ i → i ≤ j → j ≤ ((4 : ℕ) : ℤ) →
    ∃ V : Subgroup (StatedSp 2 F), (V : Set (StatedSp 2 F)) = chainProd (octGroup F) (intList i j) ∧
      V ≤ spU F ∧
      (1 < i → ∀ x ∈ octGroup F (i - 1), ∀ v ∈ V, x * v * x⁻¹ ∈ V) ∧
      (j < ((4 : ℕ) : ℤ) → ∀ x ∈ octGroup F (j + 1), ∀ v ∈ V, x * v * x⁻¹ ∈ V)
  meet_one : ∀ x ∈ spB F, x ∈ chainProd (octGroup F) ((intList 1 ((4 : ℕ) : ℤ)).map Neg.neg) →
    x = 1

end CFSG.GH74.GLS.SP
