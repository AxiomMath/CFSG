module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

open Subgroup

theorem card_eq_one_of_normalizer_le_centralizer {E : Type*} [Group E] [Finite E]
    (hE : _root_.commutator E = ⊤) (P : Sylow 2 E)
    (hN : normalizer ((P : Subgroup E) : Set E) ≤ centralizer ((P : Subgroup E) : Set E)) :
    Nat.card (P : Subgroup E) = 1 := by
  have hker : (MonoidHom.transferSylow P hN).ker = ⊤ := by
    rw [eq_top_iff, ← hE, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (hN (Subgroup.le_normalizer (MonoidHom.transferSylow P hN b).2) _
      (MonoidHom.transferSylow P hN a).2)
  have hc := MonoidHom.ker_transferSylow_isComplement' P hN
  rw [hker] at hc
  rw [(Subgroup.isComplement'_top_left.mp hc : (P : Subgroup E) = ⊥)]
  simp

end CFSG.GroupTheory.SmallFixedTwoGroup
