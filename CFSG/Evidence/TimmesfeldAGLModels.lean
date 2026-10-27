module

public import CFSG.LieType.Simplicity.Classical
public import CFSG.LieType.Simplicity.ExceptionalConverse

public section

namespace CFSG.Evidence

open CFSG.Open

theorem isSimpleGroup_of_lieModel
    {G : Type} [Group G] {t : Assembly.LowTwoRank.StatedLieTag}
    {n p f : ℕ} (h : Blueprint.LieModel G t n p f) : IsSimpleGroup G := by
  rcases h with ⟨-, h⟩ | ⟨-, ht, h⟩ | ⟨-, ht, h⟩ | ⟨-, -, h⟩
  · exact (LieType.Simplicity.fam_classical_converse G
      ((Milestones.fam_classical_model_membership_alltags G).2 ⟨t, n, p, f, h⟩)).2.2
  · exact (LieType.Simplicity.fam_exceptional_converse G (.inl ⟨t, p, f, ht, h⟩)).2.2
  · exact (LieType.Simplicity.fam_exceptional_converse G (.inr (.inl ⟨t, p, f, ht, h⟩))).2.2
  · exact (LieType.Simplicity.fam_exceptional_converse G (.inr (.inr ⟨p, f, h⟩))).2.2

end CFSG.Evidence
