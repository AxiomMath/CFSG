module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d1c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13d_cent_E0 (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    centralizer ((q13E0 t tau x₁ x₂ rho om : Subgroup G) : Set G) = ctxN tau x₁ x₂ := by
  have hX_cent : centralizer ((ctxX t tau x₁ x₂ : Subgroup G) : Set G) =
      ctxX t tau x₁ x₂ :=
    S4A.centralizer_X_of h.c11.toCtx10.toCtx4.toCtx h.c11.toCtx10.toCtx4.l43
      h.c11.toCtx10.toCtx4.l44.1
  apply le_antisymm
  · intro g hg
    have hgX : g ∈ ctxX t tau x₁ x₂ := by
      rw [← hX_cent, Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp hg) y (q13d_X_le_E0 h hy)
    have hgom : g ∈ centralizer ({om} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hg om (q13d_om_mem_E0 h)).symm
    have hmem : g ∈ ctxX t tau x₁ x₂ ⊓ centralizer ({om} : Set G) := ⟨hgX, hgom⟩
    rwa [q13a_X_om h] at hmem
  · exact Subgroup.le_centralizer_iff.mpr (q13d_E0_le_cent_N h)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
