module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0e
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARem

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau)
include hc

theorem X_le_O : ctxX t tau x₁ x₂ ≤ ctxO t tau x₁ x₂ := by
  rw [ctxX, closure_le]
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact hc.t_mem_O
  · exact hc.tau_mem_O
  · exact V_le_O hc (subset_closure (by simp))
  · exact V_le_O hc (subset_closure (by simp))

theorem CG_O_eq (hs : IsSylSL34 (ctxQ t tau x₁ x₂ rho)) :
    centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) = fourGrp x₁ x₂ := by
  refine le_antisymm ?_ ?_
  · intro g hg
    have hXO := X_le_O hc
    have hgX : g ∈ centralizer ((ctxX t tau x₁ x₂ : Subgroup G) : Set G) :=
      Subgroup.centralizer_le (fun x hx => hXO hx) hg
    rw [(Ctx4.ctxX_facts hc.toCtx4).2.2.1] at hgX
    have hmem : g ∈ ctxO t tau x₁ x₂ ⊓ centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) :=
      ⟨hXO hgX, hg⟩
    rwa [Z_O_eq hc hs] at hmem
  · intro v hv
    exact Subgroup.mem_centralizer_iff.mpr fun b hb => V_comm_O hc hb hv

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
