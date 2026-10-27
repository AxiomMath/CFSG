module

public import CFSG.GH74.Generic.BProg.B2.PumpupTable
public import CFSG.GH74.Generic.BProg.B2.PumpupTableTwoInv

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.PGV

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint Subgroup

structure Q3Cent {N : Type} [Group N] [Finite N] (H : Subgroup N) (t : N) (K : Subgroup N) :
    Prop where
  normal : H.Normal
  simple : IsSimpleGroup ↥H
  faithful : ∀ n : N, (∀ h ∈ H, n * h = h * n) → n = 1
  inv : orderOf t = 2
  comp : IsCompIn (H ⊓ centralizer ({t} : Set N)) K
  two : PumpupTableTwoInv.HasTwoInvolutions K
  type : LieModel ↥K .PSL 3 3 1

@[expose] def PuL4Any (H : Type) [Group H] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ (LieModel H .PSL 4 p f ∨ LieModel H .PSU 4 p f)

@[expose] def Q3Table : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (H : Subgroup N) (t : N) (K : Subgroup N),
    Q3Cent H t K → GHList ↥H → PuL5 ↥H ∨ PuL3sq ↥H ∨ PuL4Any ↥H

end CFSG.GH74.Generic.BProg.B2.T4.PGV
