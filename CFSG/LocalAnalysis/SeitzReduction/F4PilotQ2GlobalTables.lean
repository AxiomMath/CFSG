module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2PairTables

public section

namespace CFSG.SeitzReduction.F4Pilot

@[expose] def twoOverlapInvOrderL : Sp6Kind → ℕ
  | .field => 3840
  | .swap => 576
  | .linear6 => 192
  | .unitary6 => 576
  | .linear7 => 21504
  | .unitary7 => 82944
  | .omegaPlus8 => 96
  | .omegaMinus8 => 96

@[expose] def twoOverlapInvOrderS : Sp6Kind → ℕ
  | .field => 3840
  | .swap => 576
  | .linear6 => 96
  | .unitary6 => 96
  | .linear7 => 1536
  | .unitary7 => 4608
  | .omegaPlus8 => 576
  | .omegaMinus8 => 192

@[expose] def twoOverlapKindPairs : List (Sp6Kind × Sp6Kind) :=
  [(.field, .field), (.swap, .swap), (.linear6, .omegaMinus8), (.omegaMinus8, .linear6),
    (.unitary6, .omegaPlus8), (.omegaPlus8, .unitary6)]

@[expose] def Sp6Kind.IsGraphKind (κ : Sp6Kind) : Prop :=
  κ ≠ .field ∧ κ ≠ .swap

instance (κ : Sp6Kind) : Decidable κ.IsGraphKind :=
  inferInstanceAs (Decidable (κ ≠ .field ∧ κ ≠ .swap))

@[expose] def TwoOverlapCompat (κ κ' : Sp6Kind) : Prop :=
  twoDiagPieceOrder κ = twoDiagPieceOrder κ' ∧
    (κ.IsGraphKind → κ'.IsGraphKind → twoOverlapInvOrderL κ = twoOverlapInvOrderS κ')

instance (κ κ' : Sp6Kind) : Decidable (TwoOverlapCompat κ κ') :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem mem_twoOverlapKindPairs_of_compat {κ κ' : Sp6Kind} (h : TwoOverlapCompat κ κ') :
    (κ, κ') ∈ twoOverlapKindPairs := by
  revert h
  cases κ <;> cases κ' <;> decide

end CFSG.SeitzReduction.F4Pilot
