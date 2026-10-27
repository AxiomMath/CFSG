module

public import CFSG.Geometry.GeneralizedQuadrangles.Subquadrangle

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u}

structure IsThasQuadrangle (Γ : SimpleGraph V) [Fintype V] [DecidableRel Γ.Adj]
    (c : Γ.Coloring (Fin 2)) (q : ℕ) : Prop where
  gp : IsGeneralizedPolygon Γ 4
  thick : IsThick Γ
  two_le : 2 ≤ q
  deg : ∀ v, Γ.degree v = if c v = 0 then q ^ 3 + 1 else q ^ 2 + 1
  span : ∀ x y, c x = 0 → Γ.dist x y = 4 → (spanSet Γ x y).ncard = q + 1
  propH : ∀ u, c u = 0 → HasPropertyH Γ u

section Sub

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

@[expose] def subquadrangleColoring (c : Γ.Coloring (Fin 2)) (P' : Set V) :
    (Γ.induce (subquadrangleSet Γ c P')).Coloring (Fin 2) :=
  c.comp (SimpleGraph.Embedding.induce _).toHom

theorem subquadrangleColoring_apply (c : Γ.Coloring (Fin 2)) (P' : Set V)
    (v : subquadrangleSet Γ c P') : subquadrangleColoring c P' v = c v := rfl

end Sub

end CFSG.Geometry.GeneralizedQuadrangles
