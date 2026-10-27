module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResChief
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Open.GriessSchurMultipliersMilestoneDefs

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def gl12 : ℕ := ∏ i ∈ Finset.range 12, (2 ^ 12 - 2 ^ i)

structure EData (E : Type) [Group E] : Prop where
  chief : ChiefData E gl12
  hopf : Nat.card (griessHopfMultiplier E) ∣ 2
  outer : Group.IsSolvable (Outer E)
  nonab : ∃ a b : E, a * b ≠ b * a
  big : 256 < Nat.card E
  no3A6 : ∀ T : Subgroup E, commutator T = ⊤ → Nat.card T = 1080 → ∀ w ∈ T, orderOf w = 3 →
    (∀ t ∈ T, t * w = w * t) → False

end CFSG.EvenSporadicStandard.M24Std
