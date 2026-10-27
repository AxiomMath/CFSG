module

public import CFSG.GroupTheory.PCore.Defs
public import CFSG.LocalAnalysis.ComponentClassification.OddCore

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

theorem lit_normal_perm6 (N : Subgroup (Equiv.Perm (Fin 6))) [N.Normal] (hN : N ≠ ⊥) :
    alternatingGroup (Fin 6) ≤ N := by
  haveI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN
  exact Equiv.Perm.alternatingGroup_le_of_normal (by simp) this

section OddCore

variable (X : Type*) [Group X]

theorem lit_oddCore_eq :
    CFSG.oddCore X = CFSG.Open.componentClassificationOddCore X := rfl

theorem lit_odd_card_oddCore [Finite X] : Odd (Nat.card (CFSG.oddCore X)) :=
  CFSG.ComponentClassification.OddCore.odd_card X

theorem lit_le_oddCore {N : Subgroup X} (hN : N.Normal) (hodd : Odd (Nat.card N)) :
    N ≤ CFSG.oddCore X :=
  CFSG.ComponentClassification.OddCore.maximal X N hN hodd

theorem lit_oddCore_characteristic : (CFSG.oddCore X).Characteristic :=
  CFSG.ComponentClassification.OddCore.characteristic X

end OddCore

end CFSG.OddStandard.HigherRank.YamadaG23
