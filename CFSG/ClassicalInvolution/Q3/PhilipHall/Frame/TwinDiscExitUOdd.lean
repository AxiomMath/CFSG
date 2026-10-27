module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9Lie
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
  CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

namespace TwinDisc

@[expose] def OddCentEdge (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
    ∀ (X : Type) [Group X] [Finite X], Nat.card X < n → ∀ Φ : Set (Subgroup X), Q8Section X Φ →
      (∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) →
      (∃ M ∈ Φ, ∃ N : Subgroup X, N ∈ omegaNbr Φ M) →
        ∀ K ∈ Φ, ∀ z : X, IsUniqueInvolution K z → oddCoreImg (Subgroup.centralizer ({z} : Set X)) = ⊥

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
