module

public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

theorem lieModel_of_mulEquiv_classical {G H : Type} [Group G] [Group H] (e : G ≃* H)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (ht : t ∈ CFSG.Blueprint.classicalTags) (h : CFSG.Blueprint.LieModel H t n p f) :
    CFSG.Blueprint.LieModel G t n p f :=
  Or.inl ⟨ht, CFSG.SectionRank.statedClassicalModel_of_mulEquiv e (h.statedClassicalModel ht)⟩

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
