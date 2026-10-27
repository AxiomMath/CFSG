module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Tallini.Basic
public import CFSG.Geometry.GeneralizedQuadrangles.Subquadrangle

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

universe u

variable {V : Type u} (Γ : SimpleGraph V) [Fintype V] [DecidableRel Γ.Adj]
  (c : Γ.Coloring (Fin 2)) (q : ℕ)

@[expose] def IsThreespace (E : Set V) : Prop :=
  (∃ x, c x = 0 ∧ E = ptPerp Γ c {x}) ∨ IsFullSubquadrangle c E q

@[expose] def IsTracePlane (T : Set V) : Prop :=
  ∃ y z, c y = 0 ∧ Γ.dist y z = 4 ∧ T = traceSet Γ y z

@[expose] def IsConePlane (T : Set V) : Prop :=
  ∃ x y z, c x = 0 ∧ Γ.dist x y = 4 ∧ z ∈ traceSet Γ x y ∧ T = ptPerp Γ c {z} ∩ clSet Γ x y

@[expose] def threeBundle (T : Set V) : Set (Set V) := {E | IsThreespace Γ c q E ∧ T ⊆ E}

@[expose] def lineBundle (L : V) : Set (Set V) := {E | ∃ x, Γ.Adj L x ∧ E = ptPerp Γ c {x}}

@[expose] def IsThreeBundle (β : Set (Set V)) : Prop :=
  (∃ T, (IsTracePlane Γ c T ∨ IsConePlane Γ c T) ∧ β = threeBundle Γ c q T) ∨
    ∃ L, c L = 1 ∧ β = lineBundle Γ c L

end CFSG.Geometry.GeneralizedQuadrangles
