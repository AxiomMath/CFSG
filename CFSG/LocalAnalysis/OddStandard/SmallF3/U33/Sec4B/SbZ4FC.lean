module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4Stmt

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped Pointwise
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4Z

theorem rho_fpf (hz : Ctx4Z t L S x₁ x₂ lam rho tau) :
    ∀ a ∈ ctxQ t tau x₁ x₂ rho, rho * a * rho⁻¹ = a → a = 1 := by
  intro a ha h
  have hc : a ∈ centralizer ({rho} : Set G) :=
    mem_centralizer_iff.mpr fun x hx => by
      rw [Set.mem_singleton_iff.mp hx]
      calc rho * a = (rho * a * rho⁻¹) * rho := by group
        _ = a * rho := by rw [h]
  have hmem : a ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) := ⟨ha, hc⟩
  rw [hz.CQ_rho] at hmem
  exact mem_bot.mp hmem

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
