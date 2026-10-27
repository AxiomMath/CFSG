module

public import CFSG.GH74.Exceptional.LinearFourTwo

public section

namespace CFSG.ComponentClassification.SymmetricLocal

open CFSG.Assembly.LowTwoRank

theorem lie_model_linear_four_two_iff (Q : Type) [Group Q] :
    CFSG.Blueprint.LieModel Q .PSL 4 2 1 ↔ Nonempty (Q ≃* alternatingGroup (Fin 8)) := by
  refine ⟨CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel, ?_⟩
  rintro ⟨e⟩
  have h2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩, ZMod 2,
    inferInstance, inferInstance, by rw [h2, pow_one], ⟨?_⟩⟩
  exact e.trans (CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.trans
    (CFSG.GH74.Exceptional.statedProjStatedSLEquivOfCardTwo h2 4).symm)

end CFSG.ComponentClassification.SymmetricLocal
