module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6SF

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

@[expose] def ae6V0Letter : Fin 7 → Fin 8 := ![0, 2, 3, 4, 5, 6, 7]

@[expose] def ae6V0Index : Fin 8 → Fin 7 := ![0, 0, 1, 2, 3, 4, 5, 6]

@[expose] def ae6AEGen : Fin 7 → AE.Wr 8 :=
  ![⟨![0, 0, 1, 0, 0, 1, 1, 1], 1⟩,
    ⟨![1, 1, 0, 0, 1, 1, 0, 0], Equiv.swap 0 1 * Equiv.swap 2 7 * Equiv.swap 3 6 * Equiv.swap 4 5⟩,
    ⟨![1, 1, 0, 0, 0, 0, 1, 1], Equiv.swap 0 1 * Equiv.swap 2 5 * Equiv.swap 3 4 * Equiv.swap 6 7⟩,
    ⟨![1, 0, 0, 1, 0, 1, 0, 1], Equiv.swap 0 5 * Equiv.swap 1 2 * Equiv.swap 3 7 * Equiv.swap 4 6⟩,
    ⟨![0, 1, 0, 0, 1, 0, 1, 1], Equiv.swap 0 2 * Equiv.swap 1 7 * Equiv.swap 3 5 * Equiv.swap 4 6⟩,
    ⟨![1, 0, 1, 1, 0, 0, 0, 1], Equiv.swap 0 2 * Equiv.swap 1 5 * Equiv.swap 3 7 * Equiv.swap 4 6⟩,
    ⟨![1, 0, 0, 1, 0, 1, 0, 1], Equiv.swap 0 7 * Equiv.swap 1 2 * Equiv.swap 3 5 * Equiv.swap 4 6⟩]

@[expose] def ae6AEWord (w : List (Fin 7)) : AE.Wr 8 := (w.map ae6AEGen).prod

@[expose] def ae6Alpha0 : Finset (Fin 8) := {2, 4, 5, 7}

theorem ae6Alpha0_card : ae6Alpha0.card = 4 := by decide

@[expose] def ae6DiagTwin : Fin 2 → Fin 4 := ![3, 2]

@[expose] def AE6AE8Fin : Prop :=
  (∀ i, ae6AEGen i ∈ AE.aeSub 8) ∧
    Subgroup.closure (Set.range fun i => AE.mkQ 8 (ae6AEGen i)) = (AE.aeSub 8).map (AE.mkQ 8) ∧
    Nat.card ((AE.aeSub 8).map (AE.mkQ 8)) = 1290240 ∧ Nat.card (ae6ModelV 0) = 1290240 ∧
    Nat.card (Subgroup.closure
      (Set.range fun i => (AE.mkQ 8 (ae6AEGen i), A6.curtisGen (ae6V0Letter i)))) = 1290240 ∧
    Nat.card ae6ModelK = 8 ∧
    (∀ s : Fin 3, AE.mkQ 8 (ae6AEWord ((ae6KWord s).map ae6V0Index)) ∈
      AE.memBar ae6Alpha0 ae6Alpha0_card true) ∧
    (∀ (α : Finset (Fin 8)) (h : α.card = 4) (b : Bool) (i : Fin 7),
      ∃ (β : Finset (Fin 8)) (h' : β.card = 4) (c : Bool),
        conjSub (AE.mkQ 8 (ae6AEGen i)) (AE.memBar α h b) = AE.memBar β h' c) ∧
    (∀ (α : Finset (Fin 8)) (h : α.card = 4) (b : Bool), ∃ w : List (Fin 7),
      AE.memBar α h b = conjSub (AE.mkQ 8 (ae6AEWord w)) (AE.memBar ae6Alpha0 ae6Alpha0_card true)) ∧
    ∀ c : Fin 2, (∀ r ∈ A6.curtisRels, A6.curtisEval (List.ofFn fun i => A6.curtisGen (ae6Diag c i)) r = 1) ∧
      ∀ s : Fin 3, ae6Word ((ae6KWord s).map (ae6Diag c)) ∈ ae6Twin (ae6DiagTwin c)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
