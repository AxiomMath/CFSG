module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetBase

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

@[expose] def Thm1RTwinSetBelow (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), PhilipHall.QuaternionBridge.Q8TwinDatum R S t →
      Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2) → TightSelfGen R → TightOddFree Y →
      HypOmegaGen (CoreAssembly.conjClass (tightCore R)) →
      AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
      (∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        K' ≠ tightCore R) →
      TightInO2 t ∨ PhilipHall.Frame.TwinE4 Y ∨
        (PhilipHall.Frame.CentOmega3 Y ∧ PhilipHall.Frame.LongFundSet3 R t)

end CFSG.ClassicalInvolution.Q3.TL4
