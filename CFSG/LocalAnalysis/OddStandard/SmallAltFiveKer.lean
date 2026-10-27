module

public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveFocal

public section

namespace CFSG.OddStandard

open Subgroup Equiv CFSG.Open
open scoped Pointwise

variable {G : Type*} [Group G]

theorem le_oddCore_of_normal_odd {X : Type*} [Group X] {N : Subgroup X} (hN : N.Normal)
    (hodd : Odd (Nat.card N)) : N ≤ CFSG.oddCore X :=
  le_sSup ⟨hN, hodd⟩

section Rho

variable {L : Subgroup G} {t : G}

theorem ker_rhoOf_comp_inclusion (e : L ≃* alternatingGroup (Fin 5))
    (hHM : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) :
    ((rhoOf e).comp (inclusion hHM)).ker =
      (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)).subgroupOf
        (centralizer ({t} : Set G)) := by
  rw [inf_subgroupOf_right]
  exact ker_rhoH L t hHM e

end Rho

end CFSG.OddStandard
