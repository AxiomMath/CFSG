module

public import CFSG.Adapters.TauCetiExceptional.Interface
import CFSG.Models.Blueprint

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.TauCetiBridge

theorem models_of_blueprint_of_ne_zero {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (hn : n ≠ 0) (h : CFSG.Blueprint.LieModel X t n p f) : CFSG.Models.LieModel X t n p f :=
  CFSG.Models.LieModel.of_blueprint_of_ne_zero hn h

theorem models_of_blueprint_exceptional (hB : TypewiseBridges) {X : Type} [Group X]
    {t : StatedLieTag} {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedG2)
    (h : CFSG.Blueprint.LieModel X t 0 p f) : CFSG.Models.LieModel X t 0 p f := by
  rcases h with ⟨ht', -⟩ | ⟨-, ht', he⟩ | ⟨-, ht', hr⟩ | ⟨-, ht', -⟩
  · rcases ht with rfl | rfl | rfl <;> exact absurd ht' (by decide)
  · exact ⟨he.1, Or.inr ⟨rfl, exists_index_of_exceptional hB hp hp2 (.inl ⟨ht', he⟩)⟩⟩
  · exact ⟨hr.1, Or.inr ⟨rfl, exists_index_of_exceptional hB hp hp2 (.inr ⟨ht', hr⟩)⟩⟩
  · rcases ht with rfl | rfl | rfl <;> exact absurd ht' (by decide)

end CFSG.GH74.Generic
