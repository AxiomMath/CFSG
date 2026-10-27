module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y52Dec
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y52Excl
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y52Mod
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y52Sec
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSec5S

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y52_fact {c : Ctx5 G L} (hH : F33Hyp c.s c.e) : c.Fact52 := by
  have hd : c.d ∈ c.s.C₂ := by
    rcases y52_dec hH with h | ⟨hRT, h⟩
    · exact h
    · exact absurd h (y52_excl hH hRT)
  unfold Ctx5.Fact52
  obtain ⟨h1, h2⟩ := y52_mod hH (y52_comm_mem hH hd)
  refine ⟨h1, h2, ?_, y52_sec hH hd⟩
  rw [c.intro5.gen, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · exact f3_P_le_C₂ hH (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  · exact hd

end CFSG.OddStandard.HigherRank.YamadaG23
