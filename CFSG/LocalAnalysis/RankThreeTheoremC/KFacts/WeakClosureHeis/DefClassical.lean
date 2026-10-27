module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.LieDispatch
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.FamilyTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

section Order


theorem sdLieDef_PSL : SDLieDefAt .PSL := by
  intro K _ _ hs hnab n ℓ f hadm hmodel p hp h5 hpℓ hpK
  subst hpℓ
  obtain ⟨-, -, hrank⟩ := CFSG.SectionRank.classical_model_rank (by omega)
    (hmodel.statedClassicalModel (by decide))
  have hord := (CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput K .PSL n p f
    hadm hmodel).2.2
  by_cases h4 : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup K)
  · exact SylowDichotomyAt.of_four_le_pRank_top hp h4
  · apply SylowDichotomyAt.of_factorization_le
    rw [hord]
    rcases hrank with ⟨-, ⟨rfl, h⟩ | ⟨rfl, h⟩ | h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
    · simp only [CFSG.ComponentClassification.CatLeaf.lieSylowExponent]
      omega
    · simp only [CFSG.ComponentClassification.CatLeaf.lieSylowExponent]
      omega
    · exact absurd h h4
    · cases h
    · cases h
    · exact absurd h h4

theorem sdLieDef_PSU : SDLieDefAt .PSU := by
  intro K _ _ hs hnab n ℓ f hadm hmodel p hp h5 hpℓ hpK
  subst hpℓ
  obtain ⟨-, -, hrank⟩ := CFSG.SectionRank.classical_model_rank (by omega)
    (hmodel.statedClassicalModel (by decide))
  have hord := (CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput K .PSU n p f
    hadm hmodel).2.2
  by_cases h4 : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup K)
  · exact SylowDichotomyAt.of_four_le_pRank_top hp h4
  · apply SylowDichotomyAt.of_factorization_le
    rw [hord]
    rcases hrank with ⟨h, -⟩ | ⟨-, ⟨rfl, h⟩ | h⟩ | ⟨h, -⟩ | h
    · cases h
    · simp only [CFSG.ComponentClassification.CatLeaf.lieSylowExponent]
      omega
    · exact absurd h h4
    · cases h
    · exact absurd h h4

end Order

private theorem sdLieDef_of_orthogonal (t : StatedLieTag) (ht : t ∈ classicalTags)
    (h1 : t ≠ .PSL) (h2 : t ≠ .PSU) (h3 : t ≠ .PSp) : SDLieDefAt t := by
  intro K _ _ hs hnab n ℓ f hadm hmodel p hp h5 hpℓ hpK
  subst hpℓ
  obtain ⟨-, -, hrank⟩ := CFSG.SectionRank.classical_model_rank (by omega)
    (hmodel.statedClassicalModel ht)
  apply SylowDichotomyAt.of_four_le_pRank_top hp
  rcases hrank with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
  · exact absurd h h1
  · exact absurd h h2
  · exact absurd h h3
  · exact h

theorem sdLieDef_POmegaOdd : SDLieDefAt .POmegaOdd :=
  sdLieDef_of_orthogonal .POmegaOdd (by decide) (by decide) (by decide) (by decide)

theorem sdLieDef_POmegaPlus : SDLieDefAt .POmegaPlus :=
  sdLieDef_of_orthogonal .POmegaPlus (by decide) (by decide) (by decide) (by decide)

theorem sdLieDef_POmegaMinus : SDLieDefAt .POmegaMinus :=
  sdLieDef_of_orthogonal .POmegaMinus (by decide) (by decide) (by decide) (by decide)

theorem sdLieDef_PSp (hres : SDPsp4) : SDLieDefAt .PSp := by
  intro K _ _ hs hnab n ℓ f hadm hmodel p hp h5 hpℓ hpK
  subst hpℓ
  obtain ⟨-, hf, hrank⟩ := CFSG.SectionRank.classical_model_rank (by omega)
    (hmodel.statedClassicalModel (by decide))
  by_cases h4 : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup K)
  · exact SylowDichotomyAt.of_four_le_pRank_top hp h4
  · rcases hrank with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, ⟨rfl, h⟩ | h⟩ | h
    · cases h
    · cases h
    · have hf1 : f = 1 := by omega
      subst hf1
      exact hres K p hp h5 hmodel
    · exact absurd h h4
    · exact absurd h h4

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
