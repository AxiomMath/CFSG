module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.HeisAction

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

variable {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G]

theorem HeisCoordData.exists_of_extraspecial (Q : Subgroup G) (x y : Q)
    (hgen : Subgroup.closure ({x, y} : Set Q) = ⊤) (hcomm : commutator Q ≤ Subgroup.center Q)
    (hcard : Nat.card (Q ⧸ Subgroup.center Q) = p ^ 2) (hexp : ∀ g : Q, g ^ p = 1) :
    ∃ D : HeisCoordData p Q, D.x = x ∧ D.y = y := by
  obtain ⟨e, hx, hy⟩ := exists_coordEquiv x y hgen hcomm hcard hexp
  refine ⟨HeisCoordData.mk x y hgen
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))) hx hy ?_ ?_, rfl, rfl⟩
  · ext g
    simp
  · exact e.surjective.comp (QuotientGroup.mk'_surjective _)

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
