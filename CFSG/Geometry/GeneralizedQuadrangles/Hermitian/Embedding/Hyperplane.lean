module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Embedding.Basic

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons Module

universe u

variable {V : Type u}

section Hyperplane

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj] {c : Γ.Coloring (Fin 2)}
variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
variable {ι : V → Submodule K W} {A U : Submodule K W}

theorem exists_point_not_le_of_hyperplane (hι : IsProjGQ c ι A)
    (hU : U ≤ A) (hhyper : finrank K U + 1 = finrank K A) :
    ∃ p, c p = 0 ∧ ¬ ι p ≤ U := by
  classical
  by_contra h
  push Not at h
  have hAle : A ≤ U := by
    rw [← hι.span]
    exact iSup_le fun x => iSup_le fun hx => h x hx
  have hUA : U = A := le_antisymm hU hAle
  rw [hUA] at hhyper
  omega

theorem exists_sectionPoint_on_line [FiniteDimensional K A]
    (hι : IsProjGQ c ι A) (hU : U ≤ A)
    (hhyper : finrank K U + 1 = finrank K A) {L : V} (hL : c L = 1)
    (hLnotU : ¬ ι L ≤ U) (hLA : ι L ≤ A) :
    ∃ q, q ∈ sectionPoints c ι U ∧ Γ.Adj L q := by
  classical
  have hL2 : finrank K (ι L) = 2 := hι.finrank_line L hL
  haveI : FiniteDimensional K (ι L) := Module.finite_of_finrank_pos (by omega)
  haveI : FiniteDimensional K U := Submodule.finiteDimensional_of_le hU
  have hTleA : ι L ⊔ U ≤ A := sup_le hLA hU
  haveI : FiniteDimensional K ↥(ι L ⊔ U) := Submodule.finiteDimensional_of_le hTleA
  have hUleT : U ≤ ι L ⊔ U := le_sup_right
  have hTne : ι L ⊔ U ≠ U := by
    intro h
    exact hLnotU (le_sup_left.trans (le_of_eq h))
  have hlt : U < ι L ⊔ U := lt_of_le_of_ne hUleT (Ne.symm hTne)
  have hranklt : finrank K U < finrank K ↥(ι L ⊔ U) :=
    Submodule.finrank_lt_finrank_of_lt hlt
  have hrankle : finrank K ↥(ι L ⊔ U) ≤ finrank K A :=
    Submodule.finrank_mono hTleA
  have hT_eq_A : ι L ⊔ U = A := by
    refine Submodule.eq_of_le_of_finrank_eq hTleA ?_
    omega
  have hS1 : finrank K ↥(ι L ⊓ U) = 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (ι L) U
    rw [hT_eq_A, hL2] at h
    omega
  obtain ⟨q, hLq, hqS⟩ := hι.full L hL (ι L ⊓ U) hS1 inf_le_left
  refine ⟨q, ⟨color_eq_zero_of_adj_of_color_eq_one hL hLq, ?_⟩, hLq⟩
  rw [hqS]
  exact inf_le_right

end Hyperplane

end CFSG.Geometry.GeneralizedQuadrangles
