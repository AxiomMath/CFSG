module

public import CFSG.ClassicalInvolution.ModelFacts.E8ExclRowStmt

public section

namespace CFSG.ClassicalInvolution.RouteD.TypeE8

open CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]

@[expose] def E7LayerEquiv : Prop :=
  ∀ T ∈ F7 p f, ∃ e : {A : Subgroup (K7 p f) // A ∈ F7 p f ∧ Commutes A T} ≃ Fund12 p f,
    ∀ A A', Commutes A.1 A'.1 ↔ Commutes (e A).1 (e A').1

@[expose] def Fund12Connected : Prop :=
  ∀ R R' : Fund12 p f, Relation.ReflTransGen (fun A B : Fund12 p f => ¬ Commutes A.1 B.1) R R'

end CFSG.ClassicalInvolution.RouteD.TypeE8
