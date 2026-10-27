module

public import CFSG.Foundations.MaxOrderThompsonDefs
import CFSG.Foundations.MaxOrderThompson

public section

namespace CFSG

namespace GlaubermanReplacement

open Subgroup

@[expose, reducible] noncomputable def maxAbelianOrder (S : Type*) [Group S] [Finite S] : ℕ :=
  CFSG.maxAbelianOrder S

@[expose, reducible] noncomputable def maxOrderAbelianSubgroups (S : Type*) [Group S] [Finite S] :
    Set (Subgroup S) :=
  CFSG.maxOrderAbelianFamily S

@[expose, reducible] noncomputable def thompsonSubgroup (S : Type*) [Group S] [Finite S] :
    Subgroup S :=
  CFSG.orderThompson S

@[expose, reducible] noncomputable def thompsonCenter (S : Type*) [Group S] [Finite S] :
    Subgroup S :=
  CFSG.orderZJ S

variable {S : Type*} [Group S] [Finite S] {A : Subgroup S}

theorem mem_maxOrderAbelianSubgroups :
    A ∈ maxOrderAbelianSubgroups S ↔ IsMulCommutative A ∧ Nat.card A = maxAbelianOrder S :=
  Iff.rfl

theorem thompsonCenter_le (hA : A ∈ maxOrderAbelianSubgroups S) : thompsonCenter S ≤ A :=
  CFSG.orderZJ_le_of_mem_maxOrderAbelianFamily hA

theorem thompsonCenter_eq_iInf :
    thompsonCenter S = ⨅ A ∈ maxOrderAbelianSubgroups S, A :=
  CFSG.orderZJ_eq_iInf

end GlaubermanReplacement

end CFSG
