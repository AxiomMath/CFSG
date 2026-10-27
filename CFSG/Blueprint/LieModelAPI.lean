module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.Blueprint

open Assembly.LowTwoRank

variable {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}

theorem LieModel.classical_iff (ht : t ∈ classicalTags) :
    LieModel G t n p f ↔ StatedClassicalModel G t n p f :=
  ⟨fun h => h.statedClassicalModel ht, fun h => .inl ⟨ht, h⟩⟩

theorem LieModel.chevalleyExceptional_iff (ht : t ∈ chevalleyExceptionalTags) :
    LieModel G t n p f ↔ n = 0 ∧ ChevalleyExceptionalModel G t p f := by
  refine ⟨fun h => ⟨?_, h.chevalleyExceptionalModel ht⟩, fun ⟨hn, h⟩ => .inr (.inl ⟨hn, ht, h⟩)⟩
  rcases h with ⟨h, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
  · exact absurd h (by revert ht; cases t <;> decide)
  all_goals exact hn

theorem LieModel.reeTits_iff (ht : t ∈ reeTitsTags) :
    LieModel G t n p f ↔ n = 0 ∧ ReeTitsModel G t p f :=
  ⟨fun h => h.reeTitsModel ht, fun ⟨hn, h⟩ => .inr (.inr (.inl ⟨hn, ht, h⟩))⟩

theorem LieModel.twistedB2_iff : LieModel G .twistedB2 n p f ↔ n = 0 ∧ SuzukiModel G p f := by
  refine ⟨fun h => ?_, fun ⟨hn, h⟩ => .inr (.inr (.inr ⟨hn, rfl, h⟩))⟩
  rcases h with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨hn, -, h⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact ⟨hn, h⟩

theorem LieModel.suzukiModel (h : LieModel G .twistedB2 n p f) : n = 0 ∧ SuzukiModel G p f :=
  LieModel.twistedB2_iff.1 h

theorem LieModel.of_quotient_center (hZ : Subgroup.center G = ⊥)
    (h : LieModel (G ⧸ Subgroup.center G) t n p f) : LieModel G t n p f :=
  h.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)

theorem LieModel.quotient_center (hZ : Subgroup.center G = ⊥) (h : LieModel G t n p f) :
    LieModel (G ⧸ Subgroup.center G) t n p f :=
  h.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm

theorem LieModel.quotient_center_of_mulEquiv {G' : Type} [Group G'] (e : G ≃* G')
    (h : LieModel (G ⧸ Subgroup.center G) t n p f) :
    LieModel (G' ⧸ Subgroup.center G') t n p f :=
  h.of_mulEquiv (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e))

end CFSG.Blueprint
