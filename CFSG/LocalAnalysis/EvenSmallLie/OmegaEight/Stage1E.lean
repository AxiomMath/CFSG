module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Setup
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Orbit

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Subgroup

variable {G : Type*} [Group G]

namespace Setup

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}
  (hS : Setup ε t L U Q P a ψ p)
include hS

theorem mem_Zset_of {v w : V6} (hv : v ≠ 0) (hw : w ≠ 0) (h : qfV ε v = qfV ε w)
    (hvZ : v ∈ Zset t Q ψ) : w ∈ Zset t Q ψ := by
  obtain ⟨x, hx, rfl⟩ := hS.rad.exists_lin_eq hv hw h
  exact hS.lin_mem_Zset hx hvZ

end Setup

end CFSG.EvenSmallLie.OmegaEight.Stage1
