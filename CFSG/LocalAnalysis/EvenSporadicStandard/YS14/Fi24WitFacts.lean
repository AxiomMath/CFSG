module

public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.TranspositionGraph
public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Fi24.ExtClass

public section

namespace CFSG.EvenSporadicStandard.YS14

open CFSG.Sporadic.Fi24 (R cls D24)


@[expose] noncomputable def clsSet (Q : List (Fin 306936)) : Set R := {x | ∃ q ∈ Q, x = cls q}

@[expose] def WitFacts (r : R) : Prop :=
  r * r = 1 ∧ r ≠ 1 ∧ ∃ Q : List (Fin 306936), ∃ q₀ ∈ Q,
    (∀ q ∈ Q, r * cls q = cls q * r) ∧ r ≠ cls q₀ ∧
    evenSub (clsSet Q) ≤ ⁅evenSub (clsSet Q), evenSub (clsSet Q)⁆ ∧
    ∀ p ∈ D24, r * p = p * r → p ≠ cls q₀ →
      ∃ q ∈ Q, cls q * cls q₀ * p * (cls q * cls q₀ * p) ≠ 1

end CFSG.EvenSporadicStandard.YS14

end
