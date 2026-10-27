module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviBorelFields
public import CFSG.LieType.Universal.SpecialLinearExtras
public import CFSG.LieType.Universal.Unitary.Extras
public import CFSG.LieType.Universal.Spin.Twisted.Datum

public section

namespace CFSG.GroupTheory

@[expose] def GomiLeviFactorsSL : Prop :=
  ∀ (m : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2],
    GomiLeviFactors (CFSG.LieType.Universal.SpecialLinear.rootDatum m F)

@[expose] def GomiLeviFactorsSp : Prop :=
  ∀ (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2],
    GomiLeviFactors (CFSG.LieType.Universal.Symplectic.rootDatum n F)

@[expose] def GomiLeviFactorsSU : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ) (hF : Nat.card F = (2 ^ f) ^ 2) (n : ℕ),
    GomiLeviFactors (CFSG.LieType.Universal.Unitary.rootDatum (p := 2) hF n)

@[expose] def GomiLeviFactorsSpinPlus : Prop :=
  ∀ (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (hn : 3 ≤ n),
    GomiLeviFactors (CFSG.LieType.Universal.Spin.plusDatum n F hn)

@[expose] def GomiLeviFactorsSpinMinus : Prop :=
  ∀ (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (b c : F)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0), 4 ≤ n →
    GomiLeviFactors (CFSG.LieType.Universal.Spin.Twisted.minusDatum n hirr)

end CFSG.GroupTheory
