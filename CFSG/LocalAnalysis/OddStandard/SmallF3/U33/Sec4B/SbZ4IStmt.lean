module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4Stmt

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ctxCQ_le_ctxNQ (t tau x₁ x₂ rho : G) :
    ctxCQ t tau x₁ x₂ rho ≤ ctxNQ t tau x₁ x₂ rho :=
  centralizer_le_normalizer _

theorem conj_mem_ctxCQ {t tau x₁ x₂ rho k c : G} (hk : k ∈ ctxNQ t tau x₁ x₂ rho)
    (hc : c ∈ ctxCQ t tau x₁ x₂ rho) : k * c * k⁻¹ ∈ ctxCQ t tau x₁ x₂ rho := by
  rw [ctxCQ, mem_centralizer_iff]
  intro q hq
  have hq' : k⁻¹ * q * k ∈ ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    (mem_set_normalizer_iff''.mp hk q).mp hq
  have h1 : (k⁻¹ * q * k) * c = c * (k⁻¹ * q * k) := (mem_centralizer_iff.mp hc) _ hq'
  calc q * (k * c * k⁻¹) = k * ((k⁻¹ * q * k) * c) * k⁻¹ := by group
    _ = k * (c * (k⁻¹ * q * k)) * k⁻¹ := by rw [h1]
    _ = (k * c * k⁻¹) * q := by group

@[expose] def ctxCtI (t tau x₁ x₂ rho : G) : Subgroup G where
  carrier := {k | k ∈ ctxNQ t tau x₁ x₂ rho ∧
    k * t * k⁻¹ * t⁻¹ ∈ ctxCQ t tau x₁ x₂ rho}
  mul_mem' := by
    rintro a b ⟨ha, hac⟩ ⟨hb, hbc⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have h1 : a * b * t * (a * b)⁻¹ * t⁻¹ =
        (a * (b * t * b⁻¹ * t⁻¹) * a⁻¹) * (a * t * a⁻¹ * t⁻¹) := by group
    rw [h1]
    exact mul_mem (conj_mem_ctxCQ ha hbc) hac
  one_mem' := by
    refine ⟨one_mem _, ?_⟩
    simp
  inv_mem' := by
    rintro a ⟨ha, hac⟩
    refine ⟨inv_mem ha, ?_⟩
    have h1 : a⁻¹ * t * a⁻¹⁻¹ * t⁻¹ = a⁻¹ * (a * t * a⁻¹ * t⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [h1]
    exact conj_mem_ctxCQ (inv_mem ha) (inv_mem hac)

@[expose] def ctxEcY (t tau x₁ x₂ rho : G) : Subgroup G :=
  ctxNQ t tau x₁ x₂ rho ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G)

@[expose] def ctxKI (t tau x₁ x₂ rho : G) : Subgroup G :=
  (⁅ctxEcY t tau x₁ x₂ rho, zpowers rho⁆ ⊔ ctxCQ t tau x₁ x₂ rho) ⊓ ctxCtI t tau x₁ x₂ rho

@[expose] def L411ZIBoundStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G},
    Sec4Glob G → Sec4BInputs → Ctx4Z t L S x₁ x₂ lam rho tau →
      IsSylowIn 2 (ctxQ t tau x₁ x₂ rho) (ctxCQ t tau x₁ x₂ rho) →
        (ctxCQ t tau x₁ x₂ rho).relIndex (ctxKI t tau x₁ x₂ rho) = 1 ∨
          (ctxCQ t tau x₁ x₂ rho).relIndex (ctxKI t tau x₁ x₂ rho) = 4

@[expose] def L411ZIE4Stmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G},
    Sec4Glob G → Sec4BInputs → Ctx4Z t L S x₁ x₂ lam rho tau →
      IsSylowIn 2 (ctxQ t tau x₁ x₂ rho) (ctxCQ t tau x₁ x₂ rho) →
        (ctxCQ t tau x₁ x₂ rho).relIndex (ctxKI t tau x₁ x₂ rho) = 4 → False

@[expose] def L411ZI1Stmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G},
    Sec4Glob G → Sec4BInputs → Ctx4Z t L S x₁ x₂ lam rho tau →
      IsSylowIn 2 (ctxQ t tau x₁ x₂ rho) (ctxCQ t tau x₁ x₂ rho) →
        (ctxCQ t tau x₁ x₂ rho).relIndex (ctxKI t tau x₁ x₂ rho) = 1 → False

end CFSG.OddStandard.SmallF3.HarrisU33
