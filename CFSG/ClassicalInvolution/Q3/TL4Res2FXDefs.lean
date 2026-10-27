module

public import CFSG.ClassicalInvolution.Q3.TL4Res2FCore

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

@[expose] def ExitTwoClassR (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ J L L₀ : Subgroup G,
    F2CoreConfig J L L₀ → ∀ K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L,
      ∀ (z : G) (hz : IsUniqueInvolution K z) (W : Subgroup G) (hKW : K ≤ W),
        IsSubnormal W ⊤ → (⨆ x : W, conjSub (x : G) K) = W →
          PhilipHall.Frame.Thm4Twin.F2.ExitSec W K hKW z hz → False

end CFSG.ClassicalInvolution.Q3.TL4
