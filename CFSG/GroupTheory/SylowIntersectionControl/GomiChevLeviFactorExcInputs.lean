module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviBorelFields
public import CFSG.LieType.Steinberg.Adjoint.Presentation
public import CFSG.LieType.Steinberg.TwistedE6.Defs

public section

namespace CFSG.GroupTheory

@[expose] def GomiLeviFactorsF4 :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2],
    GomiLeviFactors (CFSG.LieType.Steinberg.Adjoint.f4Datum K)

@[expose] def GomiLeviFactorsE8 :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2],
    GomiLeviFactors (CFSG.LieType.Steinberg.Adjoint.e8Datum K)

@[expose] def GomiLeviFactorsE6 :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2],
    GomiLeviFactors (CFSG.LieType.Steinberg.Minuscule.e6Datum K)

@[expose] def GomiLeviFactorsE7 :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2],
    GomiLeviFactors (CFSG.LieType.Steinberg.Minuscule.e7Datum K)

@[expose] def GomiLeviFactorsTwistedE6 :
    Prop :=
  ∀ (k : Type) [Field k] [Finite k] [CharP k 2] (θ : k →+* k) (q : ℕ), Nat.card k = q ^ 2 →
    (∀ c, θ c = c ^ q) → GomiLeviFactors (CFSG.LieType.Steinberg.TwistedE6.twistedDatum k θ)

end CFSG.GroupTheory
