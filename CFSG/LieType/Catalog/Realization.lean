module

public import CFSG.LieType.Catalog.Existence
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LieType.Simplicity.ExceptionalConverse

public section

namespace CFSG.LieType.Catalog

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem lieModel_finite_simple
    (G : Type) [Group G] (t : StatedLieTag) (n p f : ℕ)
    (h : LieModel G t n p f) : Finite G ∧ Nontrivial G ∧ IsSimpleGroup G := by
  rcases h with ⟨-, h⟩ | ⟨-, ht, h⟩ | ⟨-, ht, h⟩ | ⟨-, -, h⟩
  · exact CFSG.LieType.Simplicity.fam_classical_converse G
      ((Milestones.fam_classical_model_membership_alltags G).2 ⟨t, n, p, f, h⟩)
  · exact CFSG.LieType.Simplicity.fam_exceptional_converse G (.inl ⟨t, p, f, ht, h⟩)
  · exact CFSG.LieType.Simplicity.fam_exceptional_converse G (.inr (.inl ⟨t, p, f, ht, h⟩))
  · exact CFSG.LieType.Simplicity.fam_exceptional_converse G (.inr (.inr ⟨p, f, h⟩))

theorem exists_lieModel_finite_simple
    (t : StatedLieTag) (n p f : ℕ)
    (hadm : StatedLieAdmissible t n p f) :
    ∃ (G : Type) (_ : Group G), Finite G ∧ Nontrivial G ∧ IsSimpleGroup G ∧
      LieModel G t n p f := by
  obtain ⟨G, _, h⟩ := cat_lie_parameter_existence t n p f hadm
  obtain ⟨h1, h2, h3⟩ := lieModel_finite_simple G t n p f h
  exact ⟨G, inferInstance, h1, h2, h3, h⟩

end CFSG.LieType.Catalog
