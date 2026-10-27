module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4I0B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4I0D
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4I0E

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem z4iPsiK_apply_coe (k : ↥(ctxKI t tau x₁ x₂ rho)) (q : ↥(ctxQ t tau x₁ x₂ rho)) :
    ((z4iPsiK t tau x₁ x₂ rho k q : ↥(ctxQ t tau x₁ x₂ rho)) : G) = (k : G) * q * (k : G)⁻¹ :=
  rfl

namespace Ctx4Z

theorem z4i_relIndex_one_or_four (hz : Ctx4Z t L S x₁ x₂ lam rho tau) :
    (ctxCQ t tau x₁ x₂ rho).relIndex (ctxKI t tau x₁ x₂ rho) = 1 ∨
      (ctxCQ t tau x₁ x₂ rho).relIndex (ctxKI t tau x₁ x₂ rho) = 4 := by
  rw [z4i_relIndex_eq_card]
  have hcomm : ∀ a b : ↥(ctxQ t tau x₁ x₂ rho), a * b = b * a :=
    fun a b => Subtype.ext (hz.Q_comm a.1 a.2 b.1 b.2)
  have h4 : ∀ q : ↥(ctxQ t tau x₁ x₂ rho), q ^ 4 = 1 := fun q =>
    Subtype.ext (by simpa using hz.Q_pow_four q.1 q.2)
  refine S4B.z4i_count hcomm h4 (z4iV t tau x₁ x₂ rho) hz.z4i_card_V ⟨x₁, hz.x₁_mem_Q⟩
    ⟨x₂, hz.x₂_mem_Q⟩ hz.z4i_hdet hz.z4iRhoBar hz.z4iTauBar hz.z4i_rhoBar_pow_three
    hz.z4i_tauBar_fixY hz.z4i_tauBar_V hz.z4i_rhoBar_comm_tauBar hz.z4i_tauBar_ne_one
    (z4iPsiK t tau x₁ x₂ rho).range ?_ ?_ ?_
  · rintro σ ⟨k, rfl⟩
    exact hz.z4iPsiK_mem_comm k
  · rintro σ ⟨k, rfl⟩ q
    rw [z4iV, Subgroup.mem_subgroupOf]
    have h := hz.z4i_comm_mem_V k.2 q.2
    simpa [z4iPsiK_apply_coe] using h
  · exact fun σ hσ => hz.z4iPsiK_conj_mem hσ

end Ctx4Z

theorem l411_zi_bound_holds : L411ZIBoundStmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau _ _ hz _
  exact hz.z4i_relIndex_one_or_four

end CFSG.OddStandard.SmallF3.HarrisU33
