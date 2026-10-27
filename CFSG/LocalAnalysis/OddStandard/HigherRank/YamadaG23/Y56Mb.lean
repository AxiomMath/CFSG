module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56Ma
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56Spl

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y56_C4_eq_M {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {M : Subgroup G}
    (hM : IsC4Cand c.s c.d M) : C4 c.s = M := by
  rw [y56_C4_eq (c := c) hH]
  exact le_antisymm (sup_le (y56_YN_le (c := c) hH hM) hM.1) (y56_M_le_YN (c := c) hH hM)

theorem y56_C4_cand (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : IsC4Cand c.s c.d (C4 c.s) := by
  obtain ⟨M, hM⟩ := y56_M_exists c hH
  rw [y56_C4_eq_M (c := c) hH hM]
  exact hM

end CFSG.OddStandard.HigherRank.YamadaG23
