module

import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.GH74.GLS.Stage2.Local.Basic
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt42

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Ctx

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem three_le_pRank_S (h : Stage2Ctx G z k S) : 3 ≤ CFSG.pRank 2 ↥S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := h.sylow_top
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hS
  obtain ⟨-, hP, hdvd⟩ := hS
  rw [Subgroup.relIndex_top_right] at hdvd
  let P : Sylow 2 G := hP.toSylow hdvd
  have hPS : (P : Subgroup G) = S := rfl
  have := (CFSG.SectionRank.pRank_sylow P).2
  rw [hPS] at this
  rw [this]
  exact h.std.rank.1

theorem not_SDorWr (hsd : SDWr_rank2) (h : Stage2Ctx G z k S) : ¬ SDorWr S := fun hS => by
  have h1 := hsd G S hS
  have h2 := three_le_pRank_S h
  omega

end Ctx

end CFSG.GH74.GLS.Stage2.Signalizer
