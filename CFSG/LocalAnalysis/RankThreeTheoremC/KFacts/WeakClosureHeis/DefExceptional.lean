module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.LieDispatch
public import CFSG.LocalAnalysis.SectionRank.ExceptionalModels
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.FamilyTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.SectionRank

theorem sdLieDef_twistedB2 : SDLieDefAt .twistedB2 := by
  intro K _ _ _ _ n ℓ f hadm _ p _ h5 hpℓ _
  obtain ⟨_, _, _, h2, _⟩ := hadm
  omega

theorem sdLieDef_twistedG2 : SDLieDefAt .twistedG2 := by
  intro K _ _ _ _ n ℓ f hadm _ p _ h5 hpℓ _
  obtain ⟨_, _, _, h3, _⟩ := hadm
  omega

theorem sdLieDef_twistedF4 : SDLieDefAt .twistedF4 := by
  intro K _ _ _ _ n ℓ f hadm _ p _ h5 hpℓ _
  obtain ⟨_, _, _, h2, _⟩ := hadm
  omega

theorem sdLieDef_Tits : SDLieDefAt .Tits := by
  intro K _ _ _ _ n ℓ f hadm _ p _ h5 hpℓ _
  obtain ⟨_, _, _, h2, _⟩ := hadm
  omega

section Rank

theorem sdLieDef_F4 : SDLieDefAt .F4 := by
  intro K _ _ _ _ n ℓ f _ hmodel p hp _ hpℓ _
  subst hpℓ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨_, hf, _⟩, hm⟩ :=
    hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  have h4 := four_mul_le_pRank_of_untwistedModel (Or.inl rfl) hm
  exact SylowDichotomyAt.of_four_le_pRank_top hp (by omega)

theorem sdLieDef_E6 : SDLieDefAt .E6 := by
  intro K _ _ _ _ n ℓ f _ hmodel p hp _ hpℓ _
  subst hpℓ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨_, hf, _⟩, hm⟩ :=
    hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  have h4 := four_mul_le_pRank_of_untwistedModel (Or.inr (Or.inl rfl)) hm
  exact SylowDichotomyAt.of_four_le_pRank_top hp (by omega)

theorem sdLieDef_E7 : SDLieDefAt .E7 := by
  intro K _ _ _ _ n ℓ f _ hmodel p hp _ hpℓ _
  subst hpℓ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨_, hf, _⟩, hm⟩ :=
    hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  have h4 := four_mul_le_pRank_of_untwistedModel (Or.inr (Or.inr (Or.inl rfl))) hm
  exact SylowDichotomyAt.of_four_le_pRank_top hp (by omega)

theorem sdLieDef_E8 : SDLieDefAt .E8 := by
  intro K _ _ _ _ n ℓ f _ hmodel p hp _ hpℓ _
  subst hpℓ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨_, hf, _⟩, hm⟩ :=
    hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  have h4 := four_mul_le_pRank_of_untwistedModel (Or.inr (Or.inr (Or.inr rfl))) hm
  exact SylowDichotomyAt.of_four_le_pRank_top hp (by omega)

theorem sdLieDef_twistedE6 : SDLieDefAt .twistedE6 := by
  intro K _ _ _ _ n ℓ f _ hmodel p hp _ hpℓ _
  subst hpℓ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨_, hf, _⟩, hm⟩ :=
    hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  exact SylowDichotomyAt.of_four_le_pRank_top hp (four_le_pRank_of_twistedE6Model hf hm)

theorem sdLieDef_trialityD4 : SDLieDefAt .trialityD4 := by
  intro K _ _ _ _ n ℓ f _ hmodel p hp _ hpℓ _
  subst hpℓ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨_, hf, _⟩, hm⟩ :=
    hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  exact SylowDichotomyAt.of_four_le_pRank_top hp (four_le_pRank_of_trialityD4Model hf hm)

theorem sdLieDef_G2 (hres : SDG2p) : SDLieDefAt .G2 := by
  intro K _ _ _ _ n ℓ f hadm hmodel p hp h5 hpℓ _
  subst hpℓ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨_, hf, _⟩, hm⟩ :=
    hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  have h3 := three_mul_le_pRank_of_G2Model hm
  by_cases hf1 : f = 1
  · subst hf1
    obtain ⟨_, _, hn0, _⟩ := hadm
    subst hn0
    exact hres K p hp h5 hmodel
  · exact SylowDichotomyAt.of_four_le_pRank_top hp (by omega)

end Rank

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
